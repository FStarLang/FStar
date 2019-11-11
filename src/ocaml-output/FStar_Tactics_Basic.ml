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
            let uu____404 =
              let uu____406 = FStar_Util.string_of_int i  in
              Prims.op_Hat "'" uu____406  in
            Prims.op_Hat b uu____404  in
          let uu____409 = f t1  in
          if uu____409 then t1 else aux (i + Prims.int_one)  in
        let uu____416 = f b  in if uu____416 then b else aux Prims.int_zero
         in
      let rec go seen subst1 bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____521 = FStar_Syntax_Subst.subst subst1 t1  in
            ((FStar_List.rev bs'), uu____521)
        | b::bs2 ->
            let b1 =
              let uu____565 = FStar_Syntax_Subst.subst_binders subst1 [b]  in
              match uu____565 with
              | b1::[] -> b1
              | uu____603 -> failwith "impossible: unshadow subst_binders"
               in
            let uu____611 = b1  in
            (match uu____611 with
             | (bv0,q) ->
                 let nbs =
                   fresh_until (s bv0)
                     (fun s1  -> Prims.op_Negation (FStar_List.mem s1 seen))
                    in
                 let bv = sset bv0 nbs  in
                 let b2 = (bv, q)  in
                 let uu____652 =
                   let uu____655 =
                     let uu____658 =
                       let uu____659 =
                         let uu____666 = FStar_Syntax_Syntax.bv_to_name bv
                            in
                         (bv0, uu____666)  in
                       FStar_Syntax_Syntax.NT uu____659  in
                     [uu____658]  in
                   FStar_List.append subst1 uu____655  in
                 go (nbs :: seen) uu____652 bs2 (b2 :: bs') t1)
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
            let uu____728 = FStar_Options.print_implicits ()  in
            if uu____728
            then
              let uu____732 = FStar_Tactics_Types.goal_env g  in
              let uu____733 = FStar_Tactics_Types.goal_witness g  in
              tts uu____732 uu____733
            else
              (let uu____736 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____736 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____742 = FStar_Tactics_Types.goal_env g  in
                   let uu____743 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____742 uu____743)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____766 = FStar_Util.string_of_int i  in
                let uu____768 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____766 uu____768
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
          let uu____792 = unshadow goal_binders goal_ty  in
          match uu____792 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____806 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____809 =
                     let uu____811 = FStar_Tactics_Types.goal_env g  in
                     tts uu____811 goal_ty1  in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____806 w uu____809)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____838 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____838
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____863 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____863
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____895 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____895
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____908 =
      let uu____909 = FStar_Tactics_Types.goal_env g  in
      let uu____910 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____909 uu____910  in
    FStar_Syntax_Util.un_squash uu____908
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____919 = get_phi g  in FStar_Option.isSome uu____919 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____943  ->
    bind get
      (fun ps  ->
         let uu____951 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____951)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____966  ->
    match uu____966 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____988 =
          let uu____992 =
            let uu____996 =
              let uu____998 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____998
                msg
               in
            let uu____1001 =
              let uu____1005 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____1009 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____1009
                else ""  in
              let uu____1015 =
                let uu____1019 =
                  let uu____1021 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____1021
                  then
                    let uu____1026 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____1026
                  else ""  in
                [uu____1019]  in
              uu____1005 :: uu____1015  in
            uu____996 :: uu____1001  in
          let uu____1036 =
            let uu____1040 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          ((Prims.int_one + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____1060 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n1)) ps g)
                ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____1040 uu____1060  in
          FStar_List.append uu____992 uu____1036  in
        FStar_String.concat "" uu____988
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____1099 = unshadow g_binders g_type  in
    match uu____1099 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____1107 =
            let uu____1108 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____1108  in
          FStar_Syntax_Print.binders_to_json uu____1107 g_binders1  in
        let uu____1109 =
          let uu____1117 =
            let uu____1125 =
              let uu____1131 =
                let uu____1132 =
                  let uu____1140 =
                    let uu____1146 =
                      let uu____1147 =
                        let uu____1149 = FStar_Tactics_Types.goal_env g  in
                        let uu____1150 = FStar_Tactics_Types.goal_witness g
                           in
                        tts uu____1149 uu____1150  in
                      FStar_Util.JsonStr uu____1147  in
                    ("witness", uu____1146)  in
                  let uu____1153 =
                    let uu____1161 =
                      let uu____1167 =
                        let uu____1168 =
                          let uu____1170 = FStar_Tactics_Types.goal_env g  in
                          tts uu____1170 g_type1  in
                        FStar_Util.JsonStr uu____1168  in
                      ("type", uu____1167)  in
                    [uu____1161;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____1140 :: uu____1153  in
                FStar_Util.JsonAssoc uu____1132  in
              ("goal", uu____1131)  in
            [uu____1125]  in
          ("hyps", j_binders) :: uu____1117  in
        FStar_Util.JsonAssoc uu____1109
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____1224  ->
    match uu____1224 with
    | (msg,ps) ->
        let uu____1234 =
          let uu____1242 =
            let uu____1250 =
              let uu____1258 =
                let uu____1266 =
                  let uu____1272 =
                    let uu____1273 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____1273  in
                  ("goals", uu____1272)  in
                let uu____1278 =
                  let uu____1286 =
                    let uu____1292 =
                      let uu____1293 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____1293  in
                    ("smt-goals", uu____1292)  in
                  [uu____1286]  in
                uu____1266 :: uu____1278  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____1258
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____1250  in
          let uu____1327 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____1343 =
                let uu____1349 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____1349)  in
              [uu____1343]
            else []  in
          FStar_List.append uu____1242 uu____1327  in
        FStar_Util.JsonAssoc uu____1234
  
let (do_dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1389  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (dump : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____1420 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          do_dump_proofstate uu____1420 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1493 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1493
          then do_dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1507 . Prims.string -> Prims.string -> 'Auu____1507 tac =
  fun msg  ->
    fun x  -> let uu____1524 = FStar_Util.format1 msg x  in fail uu____1524
  
let fail2 :
  'Auu____1535 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1535 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1559 = FStar_Util.format2 msg x y  in fail uu____1559
  
let fail3 :
  'Auu____1572 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1572 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1603 = FStar_Util.format3 msg x y z  in fail uu____1603
  
let fail4 :
  'Auu____1618 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1618 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1656 = FStar_Util.format4 msg x y z w  in
            fail uu____1656
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1691 = run t ps  in
         match uu____1691 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___229_1715 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___229_1715.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___229_1715.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___229_1715.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___229_1715.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___229_1715.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___229_1715.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___229_1715.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___229_1715.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___229_1715.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___229_1715.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___229_1715.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1754 = run t ps  in
         match uu____1754 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1802 = catch t  in
    bind uu____1802
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1829 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___255_1861  ->
              match () with
              | () -> let uu____1866 = trytac t  in run uu____1866 ps) ()
         with
         | FStar_Errors.Err (uu____1882,msg) ->
             (log ps
                (fun uu____1888  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1894,msg,uu____1896) ->
             (log ps
                (fun uu____1901  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1938 = run t ps  in
           match uu____1938 with
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
  fun p  -> mk_tac (fun uu____1962  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___290_1977 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___290_1977.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___290_1977.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___290_1977.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___290_1977.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___290_1977.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___290_1977.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___290_1977.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___290_1977.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___290_1977.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___290_1977.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___290_1977.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____2001 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____2001
         then
           let uu____2005 = FStar_Syntax_Print.term_to_string t1  in
           let uu____2007 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____2005
             uu____2007
         else ());
        (try
           (fun uu___298_2018  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____2026 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2026
                    then
                      let uu____2030 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____2032 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____2034 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____2030
                        uu____2032 uu____2034
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____2045 =
                          add_implicits g.FStar_TypeChecker_Common.implicits
                           in
                        bind uu____2045 (fun uu____2050  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____2060,msg) ->
             mlog
               (fun uu____2066  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____2069  -> ret false)
         | FStar_Errors.Error (uu____2072,msg,r) ->
             mlog
               (fun uu____2080  ->
                  let uu____2081 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____2081) (fun uu____2085  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___324_2099 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___324_2099.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred =
             (uu___324_2099.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___324_2099.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___328_2102 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___328_2102.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___328_2102.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___328_2102.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___328_2102.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___328_2102.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___328_2102.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___328_2102.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___328_2102.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___328_2102.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___328_2102.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___328_2102.FStar_Tactics_Types.local_state)
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
          (fun uu____2129  ->
             (let uu____2131 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____2131
              then
                (FStar_Options.push ();
                 (let uu____2136 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____2140 = __do_unify env t1 t2  in
              bind uu____2140
                (fun r  ->
                   (let uu____2151 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2151 then FStar_Options.pop () else ());
                   ret r)))
  
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uvs1 = FStar_Syntax_Free.uvars_uncached t1  in
        let uu____2183 = do_unify env t1 t2  in
        bind uu____2183
          (fun r  ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1  in
               let uu____2201 =
                 let uu____2203 = FStar_Util.set_eq uvs1 uvs2  in
                 Prims.op_Negation uu____2203  in
               (if uu____2201 then ret false else ret true)
             else ret false)
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___351_2226 = ps  in
         let uu____2227 =
           FStar_List.filter
             (fun g  ->
                let uu____2233 = check_goal_solved g  in
                FStar_Option.isNone uu____2233) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___351_2226.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___351_2226.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2227;
           FStar_Tactics_Types.smt_goals =
             (uu___351_2226.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___351_2226.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___351_2226.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___351_2226.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___351_2226.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___351_2226.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___351_2226.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___351_2226.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___351_2226.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2251 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____2251 with
      | FStar_Pervasives_Native.Some uu____2256 ->
          let uu____2257 =
            let uu____2259 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____2259  in
          fail uu____2257
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____2280 = FStar_Tactics_Types.goal_env goal  in
      let uu____2281 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____2280 solution uu____2281
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____2288 =
         let uu___364_2289 = p  in
         let uu____2290 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_2289.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___364_2289.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2290;
           FStar_Tactics_Types.smt_goals =
             (uu___364_2289.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_2289.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_2289.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_2289.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_2289.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_2289.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_2289.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_2289.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___364_2289.FStar_Tactics_Types.local_state)
         }  in
       set uu____2288)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____2312  ->
           let uu____2313 =
             let uu____2315 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____2315  in
           let uu____2316 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____2313 uu____2316)
        (fun uu____2321  ->
           let uu____2322 = trysolve goal solution  in
           bind uu____2322
             (fun b  ->
                if b
                then bind __dismiss (fun uu____2334  -> remove_solved_goals)
                else
                  (let uu____2337 =
                     let uu____2339 =
                       let uu____2341 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____2341 solution  in
                     let uu____2342 =
                       let uu____2344 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2345 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____2344 uu____2345  in
                     let uu____2346 =
                       let uu____2348 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2349 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____2348 uu____2349  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____2339 uu____2342 uu____2346
                      in
                   fail uu____2337)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2366 = set_solution goal solution  in
      bind uu____2366
        (fun uu____2370  ->
           bind __dismiss (fun uu____2372  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___380_2391 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___380_2391.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___380_2391.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___380_2391.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___380_2391.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___380_2391.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___380_2391.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___380_2391.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___380_2391.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___380_2391.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___380_2391.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___380_2391.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___384_2410 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___384_2410.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___384_2410.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___384_2410.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___384_2410.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___384_2410.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___384_2410.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___384_2410.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___384_2410.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___384_2410.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___384_2410.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___384_2410.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2426 = FStar_Options.defensive ()  in
    if uu____2426
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2436 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2436)
         in
      let b2 =
        b1 &&
          (let uu____2440 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2440)
         in
      let rec aux b3 e =
        let uu____2455 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2455 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2475 =
        (let uu____2479 = aux b2 env  in Prims.op_Negation uu____2479) &&
          (let uu____2482 = FStar_ST.op_Bang nwarn  in
           uu____2482 < (Prims.of_int (5)))
         in
      (if uu____2475
       then
         ((let uu____2508 =
             let uu____2509 = FStar_Tactics_Types.goal_type g  in
             uu____2509.FStar_Syntax_Syntax.pos  in
           let uu____2512 =
             let uu____2518 =
               let uu____2520 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2520
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2518)  in
           FStar_Errors.log_issue uu____2508 uu____2512);
          (let uu____2524 =
             let uu____2526 = FStar_ST.op_Bang nwarn  in
             uu____2526 + Prims.int_one  in
           FStar_ST.op_Colon_Equals nwarn uu____2524))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___406_2595 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___406_2595.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___406_2595.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___406_2595.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___406_2595.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___406_2595.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___406_2595.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___406_2595.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___406_2595.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___406_2595.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___406_2595.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___406_2595.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___411_2616 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___411_2616.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___411_2616.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___411_2616.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___411_2616.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___411_2616.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___411_2616.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___411_2616.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___411_2616.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___411_2616.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___411_2616.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___411_2616.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___416_2637 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___416_2637.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___416_2637.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___416_2637.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___416_2637.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___416_2637.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___416_2637.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___416_2637.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___416_2637.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___416_2637.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___416_2637.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___416_2637.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___421_2658 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___421_2658.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___421_2658.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___421_2658.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___421_2658.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___421_2658.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___421_2658.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___421_2658.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___421_2658.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___421_2658.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___421_2658.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___421_2658.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2670  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2701 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2701 with
        | (u,ctx_uvar,g_u) ->
            let uu____2739 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits  in
            bind uu____2739
              (fun uu____2748  ->
                 let uu____2749 =
                   let uu____2754 =
                     let uu____2755 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2755  in
                   (u, uu____2754)  in
                 ret uu____2749)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2776 = FStar_Syntax_Util.un_squash t1  in
    match uu____2776 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2788 =
          let uu____2789 = FStar_Syntax_Subst.compress t'1  in
          uu____2789.FStar_Syntax_Syntax.n  in
        (match uu____2788 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2794 -> false)
    | uu____2796 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2809 = FStar_Syntax_Util.un_squash t  in
    match uu____2809 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2820 =
          let uu____2821 = FStar_Syntax_Subst.compress t'  in
          uu____2821.FStar_Syntax_Syntax.n  in
        (match uu____2820 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2826 -> false)
    | uu____2828 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2841  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2853 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2853 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2860 = goal_to_string_verbose hd1  in
                    let uu____2862 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2860 uu____2862);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2875 =
      bind get
        (fun ps  ->
           let uu____2881 = cur_goal ()  in
           bind uu____2881
             (fun g  ->
                (let uu____2888 =
                   let uu____2889 = FStar_Tactics_Types.goal_type g  in
                   uu____2889.FStar_Syntax_Syntax.pos  in
                 let uu____2892 =
                   let uu____2898 =
                     let uu____2900 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2900
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2898)  in
                 FStar_Errors.log_issue uu____2888 uu____2892);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2875
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2923  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___466_2934 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___466_2934.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___466_2934.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___466_2934.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___466_2934.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___466_2934.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___466_2934.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___466_2934.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___466_2934.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___466_2934.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___466_2934.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___466_2934.FStar_Tactics_Types.local_state)
           }  in
         let uu____2936 = set ps1  in
         bind uu____2936
           (fun uu____2941  ->
              let uu____2942 = FStar_BigInt.of_int_fs n1  in ret uu____2942))
  
let (curms : unit -> FStar_BigInt.t tac) =
  fun uu____2950  ->
    let uu____2953 =
      let uu____2954 = FStar_Util.now_ms ()  in
      FStar_All.pipe_right uu____2954 FStar_BigInt.of_int_fs  in
    ret uu____2953
  
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
              let uu____2994 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2994 phi  in
            let uu____2995 = new_uvar reason env typ  in
            bind uu____2995
              (fun uu____3010  ->
                 match uu____3010 with
                 | (uu____3017,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1
                        in
                     ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____3064  ->
                let uu____3065 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3065)
             (fun uu____3070  ->
                let e1 =
                  let uu___485_3072 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___485_3072.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___485_3072.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___485_3072.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___485_3072.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___485_3072.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___485_3072.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___485_3072.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___485_3072.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___485_3072.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___485_3072.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___485_3072.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___485_3072.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___485_3072.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___485_3072.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___485_3072.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___485_3072.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___485_3072.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___485_3072.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___485_3072.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___485_3072.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___485_3072.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___485_3072.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___485_3072.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___485_3072.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___485_3072.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___485_3072.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___485_3072.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___485_3072.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___485_3072.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___485_3072.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___485_3072.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___485_3072.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___485_3072.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___485_3072.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___485_3072.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___485_3072.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___485_3072.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___485_3072.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___485_3072.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___485_3072.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___485_3072.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___485_3072.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___485_3072.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___485_3072.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___489_3084  ->
                     match () with
                     | () ->
                         let uu____3093 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3093) ()
                with
                | FStar_Errors.Err (uu____3120,msg) ->
                    let uu____3124 = tts e1 t  in
                    let uu____3126 =
                      let uu____3128 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3128
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3124 uu____3126 msg
                | FStar_Errors.Error (uu____3138,msg,uu____3140) ->
                    let uu____3143 = tts e1 t  in
                    let uu____3145 =
                      let uu____3147 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3147
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3143 uu____3145 msg))
  
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____3200  ->
                let uu____3201 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3201)
             (fun uu____3206  ->
                let e1 =
                  let uu___506_3208 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___506_3208.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___506_3208.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___506_3208.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___506_3208.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___506_3208.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___506_3208.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___506_3208.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___506_3208.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___506_3208.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___506_3208.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___506_3208.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___506_3208.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___506_3208.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___506_3208.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___506_3208.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___506_3208.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___506_3208.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___506_3208.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___506_3208.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___506_3208.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___506_3208.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___506_3208.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___506_3208.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___506_3208.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___506_3208.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___506_3208.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___506_3208.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___506_3208.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___506_3208.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___506_3208.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___506_3208.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___506_3208.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___506_3208.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___506_3208.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___506_3208.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___506_3208.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___506_3208.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___506_3208.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___506_3208.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___506_3208.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___506_3208.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___506_3208.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___506_3208.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___506_3208.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___510_3223  ->
                     match () with
                     | () ->
                         let uu____3232 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3232 with
                          | (t1,lc,g) ->
                              ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____3270,msg) ->
                    let uu____3274 = tts e1 t  in
                    let uu____3276 =
                      let uu____3278 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3278
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3274 uu____3276 msg
                | FStar_Errors.Error (uu____3288,msg,uu____3290) ->
                    let uu____3293 = tts e1 t  in
                    let uu____3295 =
                      let uu____3297 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3297
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3293 uu____3295 msg))
  
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____3350  ->
                let uu____3351 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3351)
             (fun uu____3357  ->
                let e1 =
                  let uu___531_3359 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___531_3359.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___531_3359.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___531_3359.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___531_3359.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___531_3359.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___531_3359.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___531_3359.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___531_3359.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___531_3359.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___531_3359.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___531_3359.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___531_3359.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___531_3359.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___531_3359.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___531_3359.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___531_3359.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___531_3359.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___531_3359.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___531_3359.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___531_3359.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___531_3359.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___531_3359.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___531_3359.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___531_3359.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___531_3359.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___531_3359.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___531_3359.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___531_3359.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___531_3359.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___531_3359.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___531_3359.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___531_3359.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___531_3359.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___531_3359.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___531_3359.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___531_3359.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___531_3359.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___531_3359.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___531_3359.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___531_3359.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___531_3359.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___531_3359.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___531_3359.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___531_3359.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                let e2 =
                  let uu___534_3362 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___534_3362.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___534_3362.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___534_3362.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___534_3362.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___534_3362.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___534_3362.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___534_3362.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___534_3362.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___534_3362.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___534_3362.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___534_3362.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___534_3362.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___534_3362.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___534_3362.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___534_3362.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___534_3362.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___534_3362.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___534_3362.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___534_3362.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___534_3362.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___534_3362.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___534_3362.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___534_3362.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___534_3362.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___534_3362.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___534_3362.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___534_3362.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___534_3362.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___534_3362.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___534_3362.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___534_3362.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___534_3362.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___534_3362.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___534_3362.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___534_3362.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___534_3362.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___534_3362.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___534_3362.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___534_3362.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___534_3362.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___534_3362.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___534_3362.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___534_3362.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___534_3362.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___538_3374  ->
                     match () with
                     | () ->
                         let uu____3383 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3383) ()
                with
                | FStar_Errors.Err (uu____3410,msg) ->
                    let uu____3414 = tts e2 t  in
                    let uu____3416 =
                      let uu____3418 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3418
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3414 uu____3416 msg
                | FStar_Errors.Error (uu____3428,msg,uu____3430) ->
                    let uu____3433 = tts e2 t  in
                    let uu____3435 =
                      let uu____3437 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3437
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3433 uu____3435 msg))
  
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
  fun uu____3471  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___559_3490 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___559_3490.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___559_3490.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___559_3490.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___559_3490.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___559_3490.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___559_3490.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___559_3490.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___559_3490.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___559_3490.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___559_3490.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___559_3490.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3515 = get_guard_policy ()  in
      bind uu____3515
        (fun old_pol  ->
           let uu____3521 = set_guard_policy pol  in
           bind uu____3521
             (fun uu____3525  ->
                bind t
                  (fun r  ->
                     let uu____3529 = set_guard_policy old_pol  in
                     bind uu____3529 (fun uu____3533  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3537 = let uu____3542 = cur_goal ()  in trytac uu____3542  in
  bind uu____3537
    (fun uu___0_3549  ->
       match uu___0_3549 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3555 = FStar_Options.peek ()  in ret uu____3555)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Common.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3580  ->
             let uu____3581 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3581)
          (fun uu____3586  ->
             let uu____3587 =
               add_implicits g.FStar_TypeChecker_Common.implicits  in
             bind uu____3587
               (fun uu____3591  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3595 =
                         let uu____3596 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3596.FStar_TypeChecker_Common.guard_f  in
                       match uu____3595 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3600 = istrivial e f  in
                           if uu____3600
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3613 =
                                          let uu____3619 =
                                            let uu____3621 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3621
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3619)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3613);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3627  ->
                                           let uu____3628 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3628)
                                        (fun uu____3633  ->
                                           let uu____3634 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3634
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___588_3642 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___588_3642.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___588_3642.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___588_3642.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___588_3642.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3646  ->
                                           let uu____3647 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3647)
                                        (fun uu____3652  ->
                                           let uu____3653 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3653
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___595_3661 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___595_3661.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___595_3661.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___595_3661.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___595_3661.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3665  ->
                                           let uu____3666 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3666)
                                        (fun uu____3670  ->
                                           try
                                             (fun uu___602_3675  ->
                                                match () with
                                                | () ->
                                                    let uu____3678 =
                                                      let uu____3680 =
                                                        let uu____3682 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3682
                                                         in
                                                      Prims.op_Negation
                                                        uu____3680
                                                       in
                                                    if uu____3678
                                                    then
                                                      mlog
                                                        (fun uu____3689  ->
                                                           let uu____3690 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3690)
                                                        (fun uu____3694  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___601_3699 ->
                                               mlog
                                                 (fun uu____3704  ->
                                                    let uu____3705 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3705)
                                                 (fun uu____3709  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun e  ->
    fun t  ->
      let uu____3726 =
        let uu____3729 = __tc_lax e t  in
        bind uu____3729
          (fun uu____3749  ->
             match uu____3749 with
             | (uu____3758,lc,uu____3760) ->
                 let uu____3761 =
                   let uu____3762 = FStar_TypeChecker_Common.lcomp_comp lc
                      in
                   FStar_All.pipe_right uu____3762
                     FStar_Pervasives_Native.fst
                    in
                 ret uu____3761)
         in
      FStar_All.pipe_left (wrap_err "tcc") uu____3726
  
let (tc : env -> FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun e  ->
    fun t  ->
      let uu____3791 =
        let uu____3796 = tcc e t  in
        bind uu____3796 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
      FStar_All.pipe_left (wrap_err "tc") uu____3791
  
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
            let uu____3848 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3848 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3860  ->
    let uu____3863 = cur_goal ()  in
    bind uu____3863
      (fun goal  ->
         let uu____3869 =
           let uu____3871 = FStar_Tactics_Types.goal_env goal  in
           let uu____3872 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3871 uu____3872  in
         if uu____3869
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3878 =
              let uu____3880 = FStar_Tactics_Types.goal_env goal  in
              let uu____3881 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3880 uu____3881  in
            fail1 "Not a trivial goal: %s" uu____3878))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3932 =
               try
                 (fun uu___661_3955  ->
                    match () with
                    | () ->
                        let uu____3966 =
                          let uu____3975 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3975
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3966) ()
               with | uu___660_3986 -> fail "divide: not enough goals"  in
             bind uu____3932
               (fun uu____4023  ->
                  match uu____4023 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___643_4049 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___643_4049.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___643_4049.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___643_4049.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___643_4049.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___643_4049.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___643_4049.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___643_4049.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___643_4049.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___643_4049.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___643_4049.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4050 = set lp  in
                      bind uu____4050
                        (fun uu____4058  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___649_4074 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___649_4074.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___649_4074.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___649_4074.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___649_4074.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___649_4074.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___649_4074.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___649_4074.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___649_4074.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___649_4074.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___649_4074.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4075 = set rp  in
                                     bind uu____4075
                                       (fun uu____4083  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___655_4099 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___655_4099.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___655_4099.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4100 = set p'
                                                       in
                                                    bind uu____4100
                                                      (fun uu____4108  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4114 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4136 = divide FStar_BigInt.one f idtac  in
    bind uu____4136
      (fun uu____4149  -> match uu____4149 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4187::uu____4188 ->
             let uu____4191 =
               let uu____4200 = map tau  in
               divide FStar_BigInt.one tau uu____4200  in
             bind uu____4191
               (fun uu____4218  ->
                  match uu____4218 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4260 =
        bind t1
          (fun uu____4265  ->
             let uu____4266 = map t2  in
             bind uu____4266 (fun uu____4274  -> ret ()))
         in
      focus uu____4260
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4284  ->
    let uu____4287 =
      let uu____4290 = cur_goal ()  in
      bind uu____4290
        (fun goal  ->
           let uu____4299 =
             let uu____4306 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4306  in
           match uu____4299 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4315 =
                 let uu____4317 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4317  in
               if uu____4315
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4326 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4326 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4342 = new_uvar "intro" env' typ'  in
                  bind uu____4342
                    (fun uu____4359  ->
                       match uu____4359 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4383 = set_solution goal sol  in
                           bind uu____4383
                             (fun uu____4389  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4391 =
                                  let uu____4394 = bnorm_goal g  in
                                  replace_cur uu____4394  in
                                bind uu____4391 (fun uu____4396  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4401 =
                 let uu____4403 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4404 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4403 uu____4404  in
               fail1 "goal is not an arrow (%s)" uu____4401)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4287
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4422  ->
    let uu____4429 = cur_goal ()  in
    bind uu____4429
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4448 =
            let uu____4455 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4455  in
          match uu____4448 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4468 =
                let uu____4470 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4470  in
              if uu____4468
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4487 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4487
                    in
                 let bs =
                   let uu____4498 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4498; b]  in
                 let env' =
                   let uu____4524 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4524 bs  in
                 let uu____4525 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4525
                   (fun uu____4551  ->
                      match uu____4551 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4565 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4568 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4565
                              FStar_Parser_Const.effect_Tot_lid uu____4568 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4586 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4586 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4608 =
                                   let uu____4609 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4609.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4608
                                  in
                               let uu____4625 = set_solution goal tm  in
                               bind uu____4625
                                 (fun uu____4634  ->
                                    let uu____4635 =
                                      let uu____4638 =
                                        bnorm_goal
                                          (let uu___726_4641 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___726_4641.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___726_4641.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___726_4641.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___726_4641.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4638  in
                                    bind uu____4635
                                      (fun uu____4648  ->
                                         let uu____4649 =
                                           let uu____4654 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4654, b)  in
                                         ret uu____4649)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4663 =
                let uu____4665 = FStar_Tactics_Types.goal_env goal  in
                let uu____4666 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4665 uu____4666  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4663))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4686 = cur_goal ()  in
    bind uu____4686
      (fun goal  ->
         mlog
           (fun uu____4693  ->
              let uu____4694 =
                let uu____4696 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4696  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4694)
           (fun uu____4702  ->
              let steps =
                let uu____4706 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4706
                 in
              let t =
                let uu____4710 = FStar_Tactics_Types.goal_env goal  in
                let uu____4711 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4710 uu____4711  in
              let uu____4712 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4712))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4737 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4745 -> g.FStar_Tactics_Types.opts
                 | uu____4748 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4753  ->
                    let uu____4754 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4754)
                 (fun uu____4759  ->
                    let uu____4760 = __tc_lax e t  in
                    bind uu____4760
                      (fun uu____4781  ->
                         match uu____4781 with
                         | (t1,uu____4791,uu____4792) ->
                             let steps =
                               let uu____4796 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4796
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4802  ->
                                  let uu____4803 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4803)
                               (fun uu____4807  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4737
  
let (refine_intro : unit -> unit tac) =
  fun uu____4820  ->
    let uu____4823 =
      let uu____4826 = cur_goal ()  in
      bind uu____4826
        (fun g  ->
           let uu____4833 =
             let uu____4844 = FStar_Tactics_Types.goal_env g  in
             let uu____4845 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4844 uu____4845
              in
           match uu____4833 with
           | (uu____4848,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4874 =
                 let uu____4879 =
                   let uu____4884 =
                     let uu____4885 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4885]  in
                   FStar_Syntax_Subst.open_term uu____4884 phi  in
                 match uu____4879 with
                 | (bvs,phi1) ->
                     let uu____4910 =
                       let uu____4911 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4911  in
                     (uu____4910, phi1)
                  in
               (match uu____4874 with
                | (bv1,phi1) ->
                    let uu____4930 =
                      let uu____4933 = FStar_Tactics_Types.goal_env g  in
                      let uu____4934 =
                        let uu____4935 =
                          let uu____4938 =
                            let uu____4939 =
                              let uu____4946 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4946)  in
                            FStar_Syntax_Syntax.NT uu____4939  in
                          [uu____4938]  in
                        FStar_Syntax_Subst.subst uu____4935 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4933
                        uu____4934 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4930
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4955  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4823
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4978 = cur_goal ()  in
      bind uu____4978
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4987 = FStar_Tactics_Types.goal_env goal  in
               let uu____4988 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4987 uu____4988
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4991 = __tc env t  in
           bind uu____4991
             (fun uu____5010  ->
                match uu____5010 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____5025  ->
                         let uu____5026 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5028 =
                           let uu____5030 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5030
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____5026 uu____5028)
                      (fun uu____5034  ->
                         let uu____5035 =
                           let uu____5038 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5038 guard  in
                         bind uu____5035
                           (fun uu____5041  ->
                              mlog
                                (fun uu____5045  ->
                                   let uu____5046 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5048 =
                                     let uu____5050 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5050
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5046 uu____5048)
                                (fun uu____5054  ->
                                   let uu____5055 =
                                     let uu____5059 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5060 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5059 typ uu____5060  in
                                   bind uu____5055
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____5070 =
                                             let uu____5072 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5072 t1  in
                                           let uu____5073 =
                                             let uu____5075 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5075 typ  in
                                           let uu____5076 =
                                             let uu____5078 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5079 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____5078 uu____5079  in
                                           let uu____5080 =
                                             let uu____5082 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5083 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____5082 uu____5083  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____5070 uu____5073 uu____5076
                                             uu____5080)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5109 =
          mlog
            (fun uu____5114  ->
               let uu____5115 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5115)
            (fun uu____5120  ->
               let uu____5121 =
                 let uu____5128 = __exact_now set_expected_typ1 tm  in
                 catch uu____5128  in
               bind uu____5121
                 (fun uu___2_5137  ->
                    match uu___2_5137 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5148  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5152  ->
                             let uu____5153 =
                               let uu____5160 =
                                 let uu____5163 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5163
                                   (fun uu____5168  ->
                                      let uu____5169 = refine_intro ()  in
                                      bind uu____5169
                                        (fun uu____5173  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5160  in
                             bind uu____5153
                               (fun uu___1_5180  ->
                                  match uu___1_5180 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5189  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5192  -> ret ())
                                  | FStar_Util.Inl uu____5193 ->
                                      mlog
                                        (fun uu____5195  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5198  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5109
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5250 = f x  in
          bind uu____5250
            (fun y  ->
               let uu____5258 = mapM f xs  in
               bind uu____5258 (fun ys  -> ret (y :: ys)))
  
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun only_match  ->
    fun acc  ->
      fun e  ->
        fun ty1  ->
          fun ty2  ->
            let f = if only_match then do_match else do_unify  in
            let uu____5368 = f e ty2 ty1  in
            bind uu____5368
              (fun uu___3_5382  ->
                 if uu___3_5382
                 then ret acc
                 else
                   (let uu____5402 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5402 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5423 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5425 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5423
                          uu____5425
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5442 =
                          let uu____5444 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5444  in
                        if uu____5442
                        then fail "Codomain is effectful"
                        else
                          (let uu____5468 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5468
                             (fun uu____5495  ->
                                match uu____5495 with
                                | (uvt,uv) ->
                                    let typ = FStar_Syntax_Util.comp_result c
                                       in
                                    let typ' =
                                      FStar_Syntax_Subst.subst
                                        [FStar_Syntax_Syntax.NT
                                           ((FStar_Pervasives_Native.fst b),
                                             uvt)] typ
                                       in
                                    __try_unify_by_application only_match
                                      ((uvt, (FStar_Pervasives_Native.snd b),
                                         uv) :: acc) e typ' ty2))))
  
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun only_match  ->
    fun e  ->
      fun ty1  ->
        fun ty2  -> __try_unify_by_application only_match [] e ty1 ty2
  
let (t_apply :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun only_match  ->
      fun tm  ->
        let uu____5601 =
          mlog
            (fun uu____5606  ->
               let uu____5607 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5607)
            (fun uu____5612  ->
               let uu____5613 = cur_goal ()  in
               bind uu____5613
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5621 = __tc e tm  in
                    bind uu____5621
                      (fun uu____5642  ->
                         match uu____5642 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5655 =
                               let uu____5666 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5666
                                in
                             bind uu____5655
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5687  ->
                                       let uu____5688 =
                                         FStar_Common.string_of_list
                                           (fun uu____5700  ->
                                              match uu____5700 with
                                              | (t,uu____5709,uu____5710) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____5688)
                                    (fun uu____5718  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____5733) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5737 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5760  ->
                                              fun w  ->
                                                match uu____5760 with
                                                | (uvt,q,uu____5778) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____5810 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5827  ->
                                              fun s  ->
                                                match uu____5827 with
                                                | (uu____5839,uu____5840,uv)
                                                    ->
                                                    let uu____5842 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____5842) uvs
                                           uu____5810
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5852 = solve' goal w  in
                                       bind uu____5852
                                         (fun uu____5857  ->
                                            let uu____5858 =
                                              mapM
                                                (fun uu____5875  ->
                                                   match uu____5875 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5887 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5887 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5892 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5893 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____5893
                                                            then ret ()
                                                            else
                                                              (let uu____5900
                                                                 =
                                                                 let uu____5903
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___893_5906
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___893_5906.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___893_5906.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___893_5906.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5903]
                                                                  in
                                                               add_goals
                                                                 uu____5900)))
                                                uvs
                                               in
                                            bind uu____5858
                                              (fun uu____5911  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5601
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5939 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5939
    then
      let uu____5948 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5963 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____6016 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5948 with
      | (pre,post) ->
          let post1 =
            let uu____6049 =
              let uu____6060 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6060]  in
            FStar_Syntax_Util.mk_app post uu____6049  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6091 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6091
       then
         let uu____6100 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6100
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
            let uu____6179 = f x e  in
            bind uu____6179 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6194 =
      let uu____6197 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6204  ->
                  let uu____6205 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6205)
               (fun uu____6211  ->
                  let is_unit_t t =
                    let uu____6219 =
                      let uu____6220 = FStar_Syntax_Subst.compress t  in
                      uu____6220.FStar_Syntax_Syntax.n  in
                    match uu____6219 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6226 -> false  in
                  let uu____6228 = cur_goal ()  in
                  bind uu____6228
                    (fun goal  ->
                       let uu____6234 =
                         let uu____6243 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6243 tm  in
                       bind uu____6234
                         (fun uu____6258  ->
                            match uu____6258 with
                            | (tm1,t,guard) ->
                                let uu____6270 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6270 with
                                 | (bs,comp) ->
                                     let uu____6303 = lemma_or_sq comp  in
                                     (match uu____6303 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6323 =
                                            fold_left
                                              (fun uu____6385  ->
                                                 fun uu____6386  ->
                                                   match (uu____6385,
                                                           uu____6386)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6537 =
                                                         is_unit_t b_t  in
                                                       if uu____6537
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
                                                         (let uu____6660 =
                                                            let uu____6667 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6667 b_t
                                                             in
                                                          bind uu____6660
                                                            (fun uu____6698 
                                                               ->
                                                               match uu____6698
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
                                          bind uu____6323
                                            (fun uu____6884  ->
                                               match uu____6884 with
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
                                                   let uu____6972 =
                                                     let uu____6976 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6977 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6978 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6976
                                                       uu____6977 uu____6978
                                                      in
                                                   bind uu____6972
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6989 =
                                                            let uu____6991 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6991
                                                              tm1
                                                             in
                                                          let uu____6992 =
                                                            let uu____6994 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6995 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____6994
                                                              uu____6995
                                                             in
                                                          let uu____6996 =
                                                            let uu____6998 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6999 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6998
                                                              uu____6999
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6989
                                                            uu____6992
                                                            uu____6996
                                                        else
                                                          (let uu____7003 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____7003
                                                             (fun uu____7011 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____7037
                                                                    =
                                                                    let uu____7040
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____7040
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____7037
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
                                                                    let uu____7076
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____7076)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____7093
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7093
                                                                  with
                                                                  | (hd1,uu____7112)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____7139)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7156
                                                                    -> false)
                                                                   in
                                                                let uu____7158
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
                                                                    let uu____7201
                                                                    = imp  in
                                                                    match uu____7201
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7212
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7212
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7234)
                                                                    ->
                                                                    let uu____7259
                                                                    =
                                                                    let uu____7260
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7260.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7259
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7268)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1008_7288
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1008_7288.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1008_7288.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1008_7288.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1008_7288.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7291
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7297
                                                                     ->
                                                                    let uu____7298
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7300
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7298
                                                                    uu____7300)
                                                                    (fun
                                                                    uu____7307
                                                                     ->
                                                                    let env =
                                                                    let uu___1013_7309
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1013_7309.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7312
                                                                    =
                                                                    let uu____7315
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7319
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7321
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7319
                                                                    uu____7321
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7327
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7315
                                                                    uu____7327
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7312
                                                                    (fun
                                                                    uu____7331
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____7158
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
                                                                    let uu____7395
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7395
                                                                    then
                                                                    let uu____7400
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7400
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
                                                                    let uu____7415
                                                                    =
                                                                    let uu____7417
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7417
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7415)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7418
                                                                    =
                                                                    let uu____7421
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7421
                                                                    guard  in
                                                                    bind
                                                                    uu____7418
                                                                    (fun
                                                                    uu____7425
                                                                     ->
                                                                    let uu____7426
                                                                    =
                                                                    let uu____7429
                                                                    =
                                                                    let uu____7431
                                                                    =
                                                                    let uu____7433
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7434
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7433
                                                                    uu____7434
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7431
                                                                     in
                                                                    if
                                                                    uu____7429
                                                                    then
                                                                    let uu____7438
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7438
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7426
                                                                    (fun
                                                                    uu____7443
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6197  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6194
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7467 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7467 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7477::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7537::uu____7538::(e1,uu____7540)::(e2,uu____7542)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7619 ->
        let uu____7622 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7622 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7636 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7636 with
              | (hd1,args) ->
                  let uu____7685 =
                    let uu____7700 =
                      let uu____7701 = FStar_Syntax_Subst.compress hd1  in
                      uu____7701.FStar_Syntax_Syntax.n  in
                    (uu____7700, args)  in
                  (match uu____7685 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7721,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7722))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____7790 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7827 = destruct_eq' typ  in
    match uu____7827 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7857 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7857 with
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
        let uu____7926 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7926 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7984 = aux e'  in
               FStar_Util.map_opt uu____7984
                 (fun uu____8015  ->
                    match uu____8015 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8041 = aux e  in
      FStar_Util.map_opt uu____8041
        (fun uu____8072  ->
           match uu____8072 with
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
          let uu____8146 =
            let uu____8157 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8157  in
          FStar_Util.map_opt uu____8146
            (fun uu____8175  ->
               match uu____8175 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1121_8197 = bv  in
                     let uu____8198 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1121_8197.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1121_8197.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____8198
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1125_8206 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____8207 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____8216 =
                       let uu____8219 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____8219  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1125_8206.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____8207;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____8216;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1125_8206.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1125_8206.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1125_8206.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1125_8206.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1128_8220 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1128_8220.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1128_8220.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1128_8220.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1128_8220.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8231 =
      let uu____8234 = cur_goal ()  in
      bind uu____8234
        (fun goal  ->
           let uu____8242 = h  in
           match uu____8242 with
           | (bv,uu____8246) ->
               mlog
                 (fun uu____8254  ->
                    let uu____8255 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8257 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8255
                      uu____8257)
                 (fun uu____8262  ->
                    let uu____8263 =
                      let uu____8274 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8274  in
                    match uu____8263 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8301 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8301 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8316 =
                               let uu____8317 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8317.FStar_Syntax_Syntax.n  in
                             (match uu____8316 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1151_8334 = bv2  in
                                    let uu____8335 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1151_8334.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1151_8334.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8335
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1155_8343 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8344 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8353 =
                                      let uu____8356 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8356
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1155_8343.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8344;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8353;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1155_8343.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1155_8343.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1155_8343.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1155_8343.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1158_8359 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1158_8359.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1158_8359.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1158_8359.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1158_8359.FStar_Tactics_Types.label)
                                     })
                              | uu____8360 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8362 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8231
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____8392 =
        let uu____8395 = cur_goal ()  in
        bind uu____8395
          (fun goal  ->
             let uu____8406 = b  in
             match uu____8406 with
             | (bv,uu____8410) ->
                 let bv' =
                   let uu____8416 =
                     let uu___1169_8417 = bv  in
                     let uu____8418 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8418;
                       FStar_Syntax_Syntax.index =
                         (uu___1169_8417.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1169_8417.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8416  in
                 let s1 =
                   let uu____8423 =
                     let uu____8424 =
                       let uu____8431 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8431)  in
                     FStar_Syntax_Syntax.NT uu____8424  in
                   [uu____8423]  in
                 let uu____8436 = subst_goal bv bv' s1 goal  in
                 (match uu____8436 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8392
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8458 =
      let uu____8461 = cur_goal ()  in
      bind uu____8461
        (fun goal  ->
           let uu____8470 = b  in
           match uu____8470 with
           | (bv,uu____8474) ->
               let uu____8479 =
                 let uu____8490 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8490  in
               (match uu____8479 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8517 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8517 with
                     | (ty,u) ->
                         let uu____8526 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8526
                           (fun uu____8545  ->
                              match uu____8545 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1193_8555 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1193_8555.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1193_8555.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8559 =
                                      let uu____8560 =
                                        let uu____8567 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8567)  in
                                      FStar_Syntax_Syntax.NT uu____8560  in
                                    [uu____8559]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1198_8579 = b1  in
                                         let uu____8580 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1198_8579.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1198_8579.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8580
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8587  ->
                                       let new_goal =
                                         let uu____8589 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8590 =
                                           let uu____8591 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8591
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8589 uu____8590
                                          in
                                       let uu____8592 = add_goals [new_goal]
                                          in
                                       bind uu____8592
                                         (fun uu____8597  ->
                                            let uu____8598 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8598
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8458
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8624 =
        let uu____8627 = cur_goal ()  in
        bind uu____8627
          (fun goal  ->
             let uu____8636 = b  in
             match uu____8636 with
             | (bv,uu____8640) ->
                 let uu____8645 =
                   let uu____8656 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8656  in
                 (match uu____8645 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8686 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8686
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1219_8691 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1219_8691.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1219_8691.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8693 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8693))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8624
  
let (revert : unit -> unit tac) =
  fun uu____8706  ->
    let uu____8709 = cur_goal ()  in
    bind uu____8709
      (fun goal  ->
         let uu____8715 =
           let uu____8722 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8722  in
         match uu____8715 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8739 =
                 let uu____8742 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8742  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8739
                in
             let uu____8757 = new_uvar "revert" env' typ'  in
             bind uu____8757
               (fun uu____8773  ->
                  match uu____8773 with
                  | (r,u_r) ->
                      let uu____8782 =
                        let uu____8785 =
                          let uu____8786 =
                            let uu____8787 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8787.FStar_Syntax_Syntax.pos  in
                          let uu____8790 =
                            let uu____8795 =
                              let uu____8796 =
                                let uu____8805 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8805  in
                              [uu____8796]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8795  in
                          uu____8790 FStar_Pervasives_Native.None uu____8786
                           in
                        set_solution goal uu____8785  in
                      bind uu____8782
                        (fun uu____8824  ->
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
      let uu____8838 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8838
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8854 = cur_goal ()  in
    bind uu____8854
      (fun goal  ->
         mlog
           (fun uu____8862  ->
              let uu____8863 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8865 =
                let uu____8867 =
                  let uu____8869 =
                    let uu____8878 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8878  in
                  FStar_All.pipe_right uu____8869 FStar_List.length  in
                FStar_All.pipe_right uu____8867 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8863 uu____8865)
           (fun uu____8899  ->
              let uu____8900 =
                let uu____8911 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8911  in
              match uu____8900 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8956 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8956
                        then
                          let uu____8961 =
                            let uu____8963 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8963
                             in
                          fail uu____8961
                        else check1 bvs2
                     in
                  let uu____8968 =
                    let uu____8970 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8970  in
                  if uu____8968
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8977 = check1 bvs  in
                     bind uu____8977
                       (fun uu____8983  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8985 =
                            let uu____8992 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8992  in
                          bind uu____8985
                            (fun uu____9002  ->
                               match uu____9002 with
                               | (ut,uvar_ut) ->
                                   let uu____9011 = set_solution goal ut  in
                                   bind uu____9011
                                     (fun uu____9016  ->
                                        let uu____9017 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____9017))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____9025  ->
    let uu____9028 = cur_goal ()  in
    bind uu____9028
      (fun goal  ->
         let uu____9034 =
           let uu____9041 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9041  in
         match uu____9034 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9050) ->
             let uu____9055 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9055)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9068 = cur_goal ()  in
    bind uu____9068
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9078 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9078  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9081  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9094 = cur_goal ()  in
    bind uu____9094
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9104 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9104  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9107  -> add_goals [g']))
  
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
            let uu____9148 = FStar_Syntax_Subst.compress t  in
            uu____9148.FStar_Syntax_Syntax.n  in
          let uu____9151 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1403_9158 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1403_9158.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1403_9158.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9151
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9175 =
                   let uu____9176 = FStar_Syntax_Subst.compress t1  in
                   uu____9176.FStar_Syntax_Syntax.n  in
                 match uu____9175 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9207 = ff hd1  in
                     bind uu____9207
                       (fun hd2  ->
                          let fa uu____9233 =
                            match uu____9233 with
                            | (a,q) ->
                                let uu____9254 = ff a  in
                                bind uu____9254 (fun a1  -> ret (a1, q))
                             in
                          let uu____9273 = mapM fa args  in
                          bind uu____9273
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9355 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9355 with
                      | (bs1,t') ->
                          let uu____9364 =
                            let uu____9367 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9367 t'  in
                          bind uu____9364
                            (fun t''  ->
                               let uu____9371 =
                                 let uu____9372 =
                                   let uu____9391 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9400 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9391, uu____9400, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9372  in
                               ret uu____9371))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9475 = ff hd1  in
                     bind uu____9475
                       (fun hd2  ->
                          let ffb br =
                            let uu____9490 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9490 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9522 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9522  in
                                let uu____9523 = ff1 e  in
                                bind uu____9523
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9538 = mapM ffb brs  in
                          bind uu____9538
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9582;
                          FStar_Syntax_Syntax.lbtyp = uu____9583;
                          FStar_Syntax_Syntax.lbeff = uu____9584;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9586;
                          FStar_Syntax_Syntax.lbpos = uu____9587;_}::[]),e)
                     ->
                     let lb =
                       let uu____9615 =
                         let uu____9616 = FStar_Syntax_Subst.compress t1  in
                         uu____9616.FStar_Syntax_Syntax.n  in
                       match uu____9615 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9620) -> lb
                       | uu____9636 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9646 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9646
                         (fun def1  ->
                            ret
                              (let uu___1356_9652 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1356_9652.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1356_9652.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1356_9652.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1356_9652.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1356_9652.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1356_9652.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9653 = fflb lb  in
                     bind uu____9653
                       (fun lb1  ->
                          let uu____9663 =
                            let uu____9668 =
                              let uu____9669 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9669]  in
                            FStar_Syntax_Subst.open_term uu____9668 e  in
                          match uu____9663 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9699 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9699  in
                              let uu____9700 = ff1 e1  in
                              bind uu____9700
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9747 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9747
                         (fun def  ->
                            ret
                              (let uu___1374_9753 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1374_9753.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1374_9753.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1374_9753.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1374_9753.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1374_9753.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1374_9753.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9754 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9754 with
                      | (lbs1,e1) ->
                          let uu____9769 = mapM fflb lbs1  in
                          bind uu____9769
                            (fun lbs2  ->
                               let uu____9781 = ff e1  in
                               bind uu____9781
                                 (fun e2  ->
                                    let uu____9789 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9789 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9860 = ff t2  in
                     bind uu____9860
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9891 = ff t2  in
                     bind uu____9891
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9898 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1398_9905 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1398_9905.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1398_9905.FStar_Syntax_Syntax.vars)
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
              let uu____9952 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1411_9961 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1411_9961.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1411_9961.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1411_9961.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1411_9961.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1411_9961.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1411_9961.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1411_9961.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1411_9961.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1411_9961.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1411_9961.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1411_9961.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1411_9961.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1411_9961.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1411_9961.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1411_9961.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1411_9961.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1411_9961.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1411_9961.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1411_9961.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1411_9961.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1411_9961.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1411_9961.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1411_9961.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1411_9961.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1411_9961.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1411_9961.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1411_9961.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1411_9961.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1411_9961.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1411_9961.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1411_9961.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1411_9961.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1411_9961.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1411_9961.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1411_9961.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___1411_9961.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1411_9961.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1411_9961.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1411_9961.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1411_9961.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1411_9961.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1411_9961.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___1411_9961.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___1411_9961.FStar_TypeChecker_Env.erasable_types_tab)
                   }) t
                 in
              match uu____9952 with
              | (t1,lcomp,g) ->
                  let uu____9968 =
                    (let uu____9972 =
                       FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp
                        in
                     Prims.op_Negation uu____9972) ||
                      (let uu____9975 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9975)
                     in
                  if uu____9968
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_TypeChecker_Common.res_typ  in
                       let uu____9986 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9986
                         (fun uu____10003  ->
                            match uu____10003 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____10016  ->
                                      let uu____10017 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____10019 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____10017 uu____10019);
                                 (let uu____10022 =
                                    let uu____10025 =
                                      let uu____10026 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10026
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____10025 opts label1
                                     in
                                  bind uu____10022
                                    (fun uu____10030  ->
                                       let uu____10031 =
                                         bind tau
                                           (fun uu____10037  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____10043  ->
                                                   let uu____10044 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____10046 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____10044 uu____10046);
                                              ret ut1)
                                          in
                                       focus uu____10031))))
                        in
                     let uu____10049 = catch rewrite_eq  in
                     bind uu____10049
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
          let uu____10261 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10261
            (fun t1  ->
               let uu____10269 =
                 f env
                   (let uu___1488_10277 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1488_10277.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1488_10277.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10269
                 (fun uu____10293  ->
                    match uu____10293 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10316 =
                               let uu____10317 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10317.FStar_Syntax_Syntax.n  in
                             match uu____10316 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10354 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10354
                                   (fun uu____10376  ->
                                      match uu____10376 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10392 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10392
                                            (fun uu____10416  ->
                                               match uu____10416 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1468_10446 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1468_10446.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1468_10446.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10488 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10488 with
                                  | (bs1,t') ->
                                      let uu____10503 =
                                        let uu____10510 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10510 ctrl1 t'
                                         in
                                      bind uu____10503
                                        (fun uu____10525  ->
                                           match uu____10525 with
                                           | (t'',ctrl2) ->
                                               let uu____10540 =
                                                 let uu____10547 =
                                                   let uu___1481_10550 = t4
                                                      in
                                                   let uu____10553 =
                                                     let uu____10554 =
                                                       let uu____10573 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10582 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10573,
                                                         uu____10582, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10554
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10553;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1481_10550.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1481_10550.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10547, ctrl2)  in
                                               ret uu____10540))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10635 -> ret (t3, ctrl1))))

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
              let uu____10681 = ctrl_tac_fold f env ctrl t  in
              bind uu____10681
                (fun uu____10702  ->
                   match uu____10702 with
                   | (t1,ctrl1) ->
                       let uu____10717 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10717
                         (fun uu____10741  ->
                            match uu____10741 with
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
                let uu____10832 =
                  let uu____10840 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10840
                    (fun uu____10851  ->
                       let uu____10852 = ctrl t1  in
                       bind uu____10852
                         (fun res  ->
                            let uu____10878 = trivial ()  in
                            bind uu____10878 (fun uu____10887  -> ret res)))
                   in
                bind uu____10832
                  (fun uu____10905  ->
                     match uu____10905 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10934 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1518_10943 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1518_10943.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1518_10943.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1518_10943.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1518_10943.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1518_10943.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1518_10943.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1518_10943.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1518_10943.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1518_10943.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1518_10943.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1518_10943.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1518_10943.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1518_10943.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1518_10943.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1518_10943.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1518_10943.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1518_10943.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1518_10943.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1518_10943.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1518_10943.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1518_10943.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1518_10943.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1518_10943.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1518_10943.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1518_10943.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1518_10943.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1518_10943.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1518_10943.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1518_10943.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1518_10943.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1518_10943.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1518_10943.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1518_10943.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1518_10943.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1518_10943.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___1518_10943.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1518_10943.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1518_10943.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1518_10943.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1518_10943.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1518_10943.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1518_10943.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___1518_10943.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___1518_10943.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t1
                               in
                            match uu____10934 with
                            | (t2,lcomp,g) ->
                                let uu____10954 =
                                  (let uu____10958 =
                                     FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10958) ||
                                    (let uu____10961 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10961)
                                   in
                                if uu____10954
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_TypeChecker_Common.res_typ
                                      in
                                   let uu____10977 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10977
                                     (fun uu____10998  ->
                                        match uu____10998 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____11015  ->
                                                  let uu____11016 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____11018 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____11016 uu____11018);
                                             (let uu____11021 =
                                                let uu____11024 =
                                                  let uu____11025 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____11025 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____11024 opts label1
                                                 in
                                              bind uu____11021
                                                (fun uu____11033  ->
                                                   let uu____11034 =
                                                     bind rewriter
                                                       (fun uu____11048  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____11054 
                                                               ->
                                                               let uu____11055
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____11057
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____11055
                                                                 uu____11057);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11034)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____11102 =
        bind get
          (fun ps  ->
             let uu____11112 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11112 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11150  ->
                       let uu____11151 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11151);
                  bind dismiss_all
                    (fun uu____11156  ->
                       let uu____11157 =
                         let uu____11164 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11164
                           keepGoing gt1
                          in
                       bind uu____11157
                         (fun uu____11174  ->
                            match uu____11174 with
                            | (gt',uu____11182) ->
                                (log ps
                                   (fun uu____11186  ->
                                      let uu____11187 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____11187);
                                 (let uu____11190 = push_goals gs  in
                                  bind uu____11190
                                    (fun uu____11195  ->
                                       let uu____11196 =
                                         let uu____11199 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____11199]  in
                                       add_goals uu____11196)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11102
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11224 =
        bind get
          (fun ps  ->
             let uu____11234 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11234 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11272  ->
                       let uu____11273 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11273);
                  bind dismiss_all
                    (fun uu____11278  ->
                       let uu____11279 =
                         let uu____11282 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11282 gt1
                          in
                       bind uu____11279
                         (fun gt'  ->
                            log ps
                              (fun uu____11290  ->
                                 let uu____11291 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11291);
                            (let uu____11294 = push_goals gs  in
                             bind uu____11294
                               (fun uu____11299  ->
                                  let uu____11300 =
                                    let uu____11303 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11303]  in
                                  add_goals uu____11300))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____11224
  
let (_trefl :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit tac) =
  fun l  ->
    fun r  ->
      let uu____11324 = cur_goal ()  in
      bind uu____11324
        (fun g  ->
           let uu____11330 =
             let uu____11334 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11334 l r  in
           bind uu____11330
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____11345 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11345 l
                      in
                   let r1 =
                     let uu____11347 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11347 r
                      in
                   let uu____11348 =
                     let uu____11352 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11352 l1 r1  in
                   bind uu____11348
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____11362 =
                             let uu____11364 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11364 l1  in
                           let uu____11365 =
                             let uu____11367 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11367 r1  in
                           fail2 "not a trivial equality ((%s) vs (%s))"
                             uu____11362 uu____11365)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11376  ->
    let uu____11379 =
      let uu____11382 = cur_goal ()  in
      bind uu____11382
        (fun g  ->
           let uu____11390 =
             let uu____11397 = FStar_Tactics_Types.goal_type g  in
             destruct_eq uu____11397  in
           match uu____11390 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11410 =
                 let uu____11412 = FStar_Tactics_Types.goal_env g  in
                 let uu____11413 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11412 uu____11413  in
               fail1 "not an equality (%s)" uu____11410)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11379
  
let (dup : unit -> unit tac) =
  fun uu____11427  ->
    let uu____11430 = cur_goal ()  in
    bind uu____11430
      (fun g  ->
         let uu____11436 =
           let uu____11443 = FStar_Tactics_Types.goal_env g  in
           let uu____11444 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11443 uu____11444  in
         bind uu____11436
           (fun uu____11454  ->
              match uu____11454 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1598_11464 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1598_11464.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1598_11464.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1598_11464.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1598_11464.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11467  ->
                       let uu____11468 =
                         let uu____11471 = FStar_Tactics_Types.goal_env g  in
                         let uu____11472 =
                           let uu____11473 =
                             let uu____11474 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11475 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11474
                               uu____11475
                              in
                           let uu____11476 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11477 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11473 uu____11476 u
                             uu____11477
                            in
                         add_irrelevant_goal "dup equation" uu____11471
                           uu____11472 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11468
                         (fun uu____11481  ->
                            let uu____11482 = add_goals [g']  in
                            bind uu____11482 (fun uu____11486  -> ret ())))))
  
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
              let uu____11612 = f x y  in
              if uu____11612 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11635 -> (acc, l11, l21)  in
        let uu____11650 = aux [] l1 l2  in
        match uu____11650 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11756 = get_phi g1  in
      match uu____11756 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11763 = get_phi g2  in
          (match uu____11763 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11776 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11776 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11807 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11807 phi1  in
                    let t2 =
                      let uu____11817 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11817 phi2  in
                    let uu____11826 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11826
                      (fun uu____11831  ->
                         let uu____11832 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11832
                           (fun uu____11839  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1649_11844 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11845 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1649_11844.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1649_11844.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1649_11844.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1649_11844.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11845;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1649_11844.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1649_11844.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1649_11844.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1649_11844.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1649_11844.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1649_11844.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1649_11844.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1649_11844.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1649_11844.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1649_11844.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1649_11844.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1649_11844.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1649_11844.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1649_11844.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1649_11844.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1649_11844.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1649_11844.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1649_11844.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1649_11844.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1649_11844.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1649_11844.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1649_11844.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1649_11844.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1649_11844.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1649_11844.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1649_11844.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1649_11844.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1649_11844.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1649_11844.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1649_11844.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1649_11844.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1649_11844.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1649_11844.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1649_11844.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1649_11844.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1649_11844.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1649_11844.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1649_11844.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1649_11844.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let uu____11849 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11849
                                (fun goal  ->
                                   mlog
                                     (fun uu____11859  ->
                                        let uu____11860 =
                                          goal_to_string_verbose g1  in
                                        let uu____11862 =
                                          goal_to_string_verbose g2  in
                                        let uu____11864 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11860 uu____11862 uu____11864)
                                     (fun uu____11868  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11876  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11892 =
               set
                 (let uu___1664_11897 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1664_11897.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1664_11897.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1664_11897.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1664_11897.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1664_11897.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1664_11897.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1664_11897.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1664_11897.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1664_11897.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1664_11897.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1664_11897.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11892
               (fun uu____11900  ->
                  let uu____11901 = join_goals g1 g2  in
                  bind uu____11901 (fun g12  -> add_goals [g12]))
         | uu____11906 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11922 =
      let uu____11925 = cur_goal ()  in
      bind uu____11925
        (fun g  ->
           FStar_Options.push ();
           (let uu____11938 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11938);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1675_11945 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1675_11945.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1675_11945.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1675_11945.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1675_11945.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11922
  
let (top_env : unit -> env tac) =
  fun uu____11962  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11977  ->
    let uu____11981 = cur_goal ()  in
    bind uu____11981
      (fun g  ->
         let uu____11988 =
           (FStar_Options.lax ()) ||
             (let uu____11991 = FStar_Tactics_Types.goal_env g  in
              uu____11991.FStar_TypeChecker_Env.lax)
            in
         ret uu____11988)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____12008 =
        mlog
          (fun uu____12013  ->
             let uu____12014 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____12014)
          (fun uu____12019  ->
             let uu____12020 = cur_goal ()  in
             bind uu____12020
               (fun goal  ->
                  let env =
                    let uu____12028 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12028 ty  in
                  let uu____12029 = __tc_ghost env tm  in
                  bind uu____12029
                    (fun uu____12048  ->
                       match uu____12048 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12062  ->
                                let uu____12063 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12063)
                             (fun uu____12067  ->
                                mlog
                                  (fun uu____12070  ->
                                     let uu____12071 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12071)
                                  (fun uu____12076  ->
                                     let uu____12077 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12077
                                       (fun uu____12082  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____12008
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12107 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12113 =
              let uu____12120 =
                let uu____12121 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12121
                 in
              new_uvar "uvar_env.2" env uu____12120  in
            bind uu____12113
              (fun uu____12138  ->
                 match uu____12138 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12107
        (fun typ  ->
           let uu____12150 = new_uvar "uvar_env" env typ  in
           bind uu____12150
             (fun uu____12165  ->
                match uu____12165 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12184 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12203 -> g.FStar_Tactics_Types.opts
             | uu____12206 -> FStar_Options.peek ()  in
           let uu____12209 = FStar_Syntax_Util.head_and_args t  in
           match uu____12209 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12229);
                FStar_Syntax_Syntax.pos = uu____12230;
                FStar_Syntax_Syntax.vars = uu____12231;_},uu____12232)
               ->
               let env1 =
                 let uu___1729_12274 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1729_12274.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1729_12274.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1729_12274.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1729_12274.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1729_12274.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1729_12274.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1729_12274.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1729_12274.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1729_12274.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1729_12274.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1729_12274.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1729_12274.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1729_12274.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1729_12274.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1729_12274.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1729_12274.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1729_12274.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1729_12274.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1729_12274.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1729_12274.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1729_12274.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1729_12274.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1729_12274.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1729_12274.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1729_12274.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1729_12274.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1729_12274.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1729_12274.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1729_12274.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1729_12274.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1729_12274.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1729_12274.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1729_12274.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1729_12274.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1729_12274.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1729_12274.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1729_12274.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1729_12274.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1729_12274.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1729_12274.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1729_12274.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1729_12274.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1729_12274.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1729_12274.FStar_TypeChecker_Env.erasable_types_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12278 =
                 let uu____12281 = bnorm_goal g  in [uu____12281]  in
               add_goals uu____12278
           | uu____12282 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12184
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12344 = if b then t2 else ret false  in
             bind uu____12344 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12370 = trytac comp  in
      bind uu____12370
        (fun uu___4_12382  ->
           match uu___4_12382 with
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
        let uu____12424 =
          bind get
            (fun ps  ->
               let uu____12432 = __tc e t1  in
               bind uu____12432
                 (fun uu____12453  ->
                    match uu____12453 with
                    | (t11,ty1,g1) ->
                        let uu____12466 = __tc e t2  in
                        bind uu____12466
                          (fun uu____12487  ->
                             match uu____12487 with
                             | (t21,ty2,g2) ->
                                 let uu____12500 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12500
                                   (fun uu____12507  ->
                                      let uu____12508 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12508
                                        (fun uu____12516  ->
                                           let uu____12517 =
                                             do_unify e ty1 ty2  in
                                           let uu____12521 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12517 uu____12521)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12424
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12569  ->
             let uu____12570 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12570
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
        (fun uu____12604  ->
           let uu____12605 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12605)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12616 =
      mlog
        (fun uu____12621  ->
           let uu____12622 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12622)
        (fun uu____12627  ->
           let uu____12628 = cur_goal ()  in
           bind uu____12628
             (fun g  ->
                let uu____12634 =
                  let uu____12643 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12643 ty  in
                bind uu____12634
                  (fun uu____12655  ->
                     match uu____12655 with
                     | (ty1,uu____12665,guard) ->
                         let uu____12667 =
                           let uu____12670 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12670 guard  in
                         bind uu____12667
                           (fun uu____12674  ->
                              let uu____12675 =
                                let uu____12679 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12680 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12679 uu____12680 ty1  in
                              bind uu____12675
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12689 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12689
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12696 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12697 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12696
                                          uu____12697
                                         in
                                      let nty =
                                        let uu____12699 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12699 ty1  in
                                      let uu____12700 =
                                        let uu____12704 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12704 ng nty  in
                                      bind uu____12700
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12713 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12713
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12616
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12787 =
      let uu____12796 = cur_goal ()  in
      bind uu____12796
        (fun g  ->
           let uu____12808 =
             let uu____12817 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12817 s_tm  in
           bind uu____12808
             (fun uu____12835  ->
                match uu____12835 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12853 =
                      let uu____12856 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12856 guard  in
                    bind uu____12853
                      (fun uu____12870  ->
                         let s_ty1 =
                           let uu____12872 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant]
                             uu____12872 s_ty
                            in
                         let uu____12873 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____12873 with
                         | (h,args) ->
                             let uu____12918 =
                               let uu____12925 =
                                 let uu____12926 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12926.FStar_Syntax_Syntax.n  in
                               match uu____12925 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12941;
                                      FStar_Syntax_Syntax.vars = uu____12942;_},us)
                                   -> ret (fv, us)
                               | uu____12952 -> fail "type is not an fv"  in
                             bind uu____12918
                               (fun uu____12973  ->
                                  match uu____12973 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12989 =
                                        let uu____12992 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12992 t_lid
                                         in
                                      (match uu____12989 with
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                let erasable1 =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr
                                                   in
                                                let uu____13033 =
                                                  erasable1 &&
                                                    (let uu____13036 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____13036)
                                                   in
                                                failwhen uu____13033
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____13046  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____13059  ->
                                                          let uu____13060 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____13060
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____13075
                                                                =
                                                                mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____13103
                                                                    =
                                                                    let uu____13106
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13106
                                                                    c_lid  in
                                                                    match uu____13103
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
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
                                                                    uu____13180
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
                                                                    let uu____13185
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13185
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13208
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13208
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13251
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____13251
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____13324
                                                                    =
                                                                    let uu____13326
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____13326
                                                                     in
                                                                    failwhen
                                                                    uu____13324
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13345
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
                                                                    uu___5_13362
                                                                    =
                                                                    match uu___5_13362
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13366)
                                                                    -> true
                                                                    | 
                                                                    uu____13369
                                                                    -> false
                                                                     in
                                                                    let uu____13373
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13373
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
                                                                    uu____13509
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
                                                                    uu____13571
                                                                     ->
                                                                    match uu____13571
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13591),
                                                                    (t,uu____13593))
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
                                                                    uu____13663
                                                                     ->
                                                                    match uu____13663
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13690),
                                                                    (t,uu____13692))
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
                                                                    uu____13751
                                                                     ->
                                                                    match uu____13751
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
                                                                    env s_ty1
                                                                     in
                                                                    let uu____13806
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1896_13830
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1896_13830.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____13806
                                                                    with
                                                                    | 
                                                                    (uu____13844,uu____13845,uu____13846,uu____13847,pat_t,uu____13849,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13863
                                                                    =
                                                                    let uu____13864
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13864
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13863
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13869
                                                                    =
                                                                    let uu____13878
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13878]
                                                                     in
                                                                    let uu____13897
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13869
                                                                    uu____13897
                                                                     in
                                                                    let nty =
                                                                    let uu____13903
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13903
                                                                     in
                                                                    let uu____13906
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13906
                                                                    (fun
                                                                    uu____13936
                                                                     ->
                                                                    match uu____13936
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
                                                                    let uu____13963
                                                                    =
                                                                    let uu____13974
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13974]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13963
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____14010
                                                                    =
                                                                    let uu____14021
                                                                    =
                                                                    let uu____14026
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____14026)
                                                                     in
                                                                    (g', br,
                                                                    uu____14021)
                                                                     in
                                                                    ret
                                                                    uu____14010))))))
                                                                    | 
                                                                    uu____14047
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              bind
                                                                uu____13075
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____14097
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____14097
                                                                   with
                                                                   | 
                                                                   (goals,brs,infos)
                                                                    ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let uu____14170
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    bind
                                                                    uu____14170
                                                                    (fun
                                                                    uu____14181
                                                                     ->
                                                                    let uu____14182
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14182
                                                                    (fun
                                                                    uu____14192
                                                                     ->
                                                                    ret infos)))))
                                            | uu____14199 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12787
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14248::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14278 = init xs  in x :: uu____14278
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14291 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14300) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14366 = last args  in
          (match uu____14366 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14396 =
                 let uu____14397 =
                   let uu____14402 =
                     let uu____14403 =
                       let uu____14408 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14408  in
                     uu____14403 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14402, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14397  in
               FStar_All.pipe_left ret uu____14396)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14419,uu____14420) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14473 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14473 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14515 =
                      let uu____14516 =
                        let uu____14521 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14521)  in
                      FStar_Reflection_Data.Tv_Abs uu____14516  in
                    FStar_All.pipe_left ret uu____14515))
      | FStar_Syntax_Syntax.Tm_type uu____14524 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14549 ->
          let uu____14564 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14564 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14595 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14595 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14648 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14661 =
            let uu____14662 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14662  in
          FStar_All.pipe_left ret uu____14661
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14683 =
            let uu____14684 =
              let uu____14689 =
                let uu____14690 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14690  in
              (uu____14689, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14684  in
          FStar_All.pipe_left ret uu____14683
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14730 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14735 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14735 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14788 ->
                            failwith
                              "impossible: open_term returned different amount of binders"
                         in
                      FStar_All.pipe_left ret
                        (FStar_Reflection_Data.Tv_Let
                           (false, (lb.FStar_Syntax_Syntax.lbattrs),
                             (FStar_Pervasives_Native.fst b1),
                             (lb.FStar_Syntax_Syntax.lbdef), t22))))
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14832 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14836 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14836 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14856 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true,
                                       (lb1.FStar_Syntax_Syntax.lbattrs),
                                       bv1, (lb1.FStar_Syntax_Syntax.lbdef),
                                       t22)))
                       | uu____14864 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14919 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14919
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14940 =
                  let uu____14952 =
                    FStar_List.map
                      (fun uu____14976  ->
                         match uu____14976 with
                         | (p1,b) ->
                             let uu____14997 = inspect_pat p1  in
                             (uu____14997, b)) ps
                     in
                  (fv, uu____14952)  in
                FStar_Reflection_Data.Pat_Cons uu____14940
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
              (fun uu___6_15093  ->
                 match uu___6_15093 with
                 | (pat,uu____15115,t5) ->
                     let uu____15133 = inspect_pat pat  in (uu____15133, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____15142 ->
          ((let uu____15144 =
              let uu____15150 =
                let uu____15152 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15154 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15152 uu____15154
                 in
              (FStar_Errors.Warning_CantInspect, uu____15150)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15144);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14291
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15172 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15172
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15176 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15176
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15180 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15180
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15187 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15187
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15212 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15212
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15229 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15229
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15248 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15248
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15252 =
          let uu____15253 =
            let uu____15260 =
              let uu____15261 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15261  in
            FStar_Syntax_Syntax.mk uu____15260  in
          uu____15253 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15252
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15266 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15266
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15280 =
          let uu____15281 =
            let uu____15288 =
              let uu____15289 =
                let uu____15303 =
                  let uu____15306 =
                    let uu____15307 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15307]  in
                  FStar_Syntax_Subst.close uu____15306 t2  in
                ((false, [lb]), uu____15303)  in
              FStar_Syntax_Syntax.Tm_let uu____15289  in
            FStar_Syntax_Syntax.mk uu____15288  in
          uu____15281 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15280
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15352 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15352 with
         | (lbs,body) ->
             let uu____15367 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15367)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15404 =
                let uu____15405 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15405  in
              FStar_All.pipe_left wrap uu____15404
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15422 =
                let uu____15423 =
                  let uu____15437 =
                    FStar_List.map
                      (fun uu____15461  ->
                         match uu____15461 with
                         | (p1,b) ->
                             let uu____15476 = pack_pat p1  in
                             (uu____15476, b)) ps
                     in
                  (fv, uu____15437)  in
                FStar_Syntax_Syntax.Pat_cons uu____15423  in
              FStar_All.pipe_left wrap uu____15422
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
            (fun uu___7_15524  ->
               match uu___7_15524 with
               | (pat,t1) ->
                   let uu____15541 = pack_pat pat  in
                   (uu____15541, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15589 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15589
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15617 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15617
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15663 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15663
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15702 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15702
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15722 =
        bind get
          (fun ps  ->
             let uu____15728 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15728 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15722
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15762 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2200_15769 = ps  in
                 let uu____15770 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2200_15769.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2200_15769.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2200_15769.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2200_15769.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2200_15769.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2200_15769.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2200_15769.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2200_15769.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2200_15769.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2200_15769.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2200_15769.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15770
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15762
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15797 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15797 with
      | (u,ctx_uvars,g_u) ->
          let uu____15830 = FStar_List.hd ctx_uvars  in
          (match uu____15830 with
           | (ctx_uvar,uu____15844) ->
               let g =
                 let uu____15846 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15846 false
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____15855 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____15855 with
    | (env1,uu____15863) ->
        let env2 =
          let uu___2217_15869 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2217_15869.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2217_15869.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2217_15869.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2217_15869.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2217_15869.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2217_15869.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2217_15869.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2217_15869.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2217_15869.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2217_15869.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___2217_15869.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2217_15869.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2217_15869.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2217_15869.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2217_15869.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2217_15869.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2217_15869.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2217_15869.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2217_15869.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2217_15869.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2217_15869.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2217_15869.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2217_15869.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2217_15869.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2217_15869.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2217_15869.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2217_15869.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2217_15869.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2217_15869.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2217_15869.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2217_15869.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2217_15869.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2217_15869.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2217_15869.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2217_15869.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2217_15869.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2217_15869.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2217_15869.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2217_15869.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2217_15869.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2217_15869.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2217_15869.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2217_15869.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2217_15869.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env3 =
          let uu___2220_15872 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2220_15872.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2220_15872.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2220_15872.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2220_15872.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2220_15872.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2220_15872.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2220_15872.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2220_15872.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2220_15872.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2220_15872.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2220_15872.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2220_15872.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2220_15872.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2220_15872.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2220_15872.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2220_15872.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2220_15872.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2220_15872.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2220_15872.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2220_15872.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2220_15872.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2220_15872.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___2220_15872.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2220_15872.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2220_15872.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2220_15872.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2220_15872.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2220_15872.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2220_15872.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2220_15872.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2220_15872.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2220_15872.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2220_15872.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2220_15872.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2220_15872.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2220_15872.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2220_15872.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2220_15872.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2220_15872.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2220_15872.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2220_15872.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2220_15872.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2220_15872.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2220_15872.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env4 =
          let uu___2223_15875 = env3  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2223_15875.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2223_15875.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2223_15875.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2223_15875.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2223_15875.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2223_15875.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2223_15875.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2223_15875.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2223_15875.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2223_15875.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2223_15875.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2223_15875.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2223_15875.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2223_15875.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2223_15875.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2223_15875.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2223_15875.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2223_15875.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2223_15875.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2223_15875.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2223_15875.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2223_15875.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2223_15875.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2223_15875.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2223_15875.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2223_15875.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2223_15875.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2223_15875.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2223_15875.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2223_15875.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2223_15875.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2223_15875.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2223_15875.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2223_15875.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2223_15875.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2223_15875.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2223_15875.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2223_15875.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2223_15875.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2223_15875.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2223_15875.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2223_15875.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2223_15875.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2223_15875.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        env4
  
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng  ->
    fun env  ->
      fun goals  ->
        fun imps  ->
          let env1 = tac_env env  in
          let ps =
            let uu____15908 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____15911 = FStar_Util.psmap_empty ()  in
            {
              FStar_Tactics_Types.main_context = env1;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump = do_dump_proofstate;
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu____15908;
              FStar_Tactics_Types.local_state = uu____15911
            }  in
          ps
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let env1 = tac_env env  in
        let uu____15937 = goal_of_goal_ty env1 typ  in
        match uu____15937 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Common.implicits
               in
            let uu____15949 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15949)
  