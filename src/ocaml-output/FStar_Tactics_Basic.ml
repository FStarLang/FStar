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
<<<<<<< HEAD
          (fun uu____3566  ->
             let uu____3567 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3567)
          (fun uu____3572  ->
             let uu____3573 =
               add_implicits g.FStar_TypeChecker_Common.implicits  in
             bind uu____3573
               (fun uu____3577  ->
=======
          (fun uu____3580  ->
             let uu____3581 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3581)
          (fun uu____3586  ->
             let uu____3587 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3587
               (fun uu____3591  ->
>>>>>>> snap
                  bind getopts
                    (fun opts  ->
                       let uu____3595 =
                         let uu____3596 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
<<<<<<< HEAD
                         uu____3582.FStar_TypeChecker_Common.guard_f  in
                       match uu____3581 with
=======
                         uu____3596.FStar_TypeChecker_Env.guard_f  in
                       match uu____3595 with
>>>>>>> snap
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
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____3721 =
      let uu____3724 = cur_goal ()  in
      bind uu____3724
        (fun goal  ->
<<<<<<< HEAD
           let uu____3716 =
             let uu____3725 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3725 t  in
           bind uu____3716
             (fun uu____3737  ->
                match uu____3737 with
                | (uu____3746,lc,uu____3748) ->
                    let uu____3749 =
                      let uu____3750 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      FStar_All.pipe_right uu____3750
                        FStar_Pervasives_Native.fst
                       in
                    ret uu____3749))
=======
           let uu____3730 =
             let uu____3739 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3739 t  in
           bind uu____3730
             (fun uu____3751  ->
                match uu____3751 with
                | (uu____3760,lc,uu____3762) ->
                    let uu____3763 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____3763))
>>>>>>> snap
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____3721
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
<<<<<<< HEAD
    let uu____3774 =
      let uu____3779 = tcc t  in
      bind uu____3779 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3774
=======
    let uu____3779 =
      let uu____3784 = tcc t  in
      bind uu____3784 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3779
>>>>>>> snap
  
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
<<<<<<< HEAD
            let uu____3831 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3831 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3843  ->
    let uu____3846 = cur_goal ()  in
    bind uu____3846
      (fun goal  ->
         let uu____3852 =
           let uu____3854 = FStar_Tactics_Types.goal_env goal  in
           let uu____3855 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3854 uu____3855  in
         if uu____3852
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3861 =
              let uu____3863 = FStar_Tactics_Types.goal_env goal  in
              let uu____3864 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3863 uu____3864  in
            fail1 "Not a trivial goal: %s" uu____3861))
=======
            let uu____3836 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3836 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3848  ->
    let uu____3851 = cur_goal ()  in
    bind uu____3851
      (fun goal  ->
         let uu____3857 =
           let uu____3859 = FStar_Tactics_Types.goal_env goal  in
           let uu____3860 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3859 uu____3860  in
         if uu____3857
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3866 =
              let uu____3868 = FStar_Tactics_Types.goal_env goal  in
              let uu____3869 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3868 uu____3869  in
            fail1 "Not a trivial goal: %s" uu____3866))
>>>>>>> snap
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
<<<<<<< HEAD
             let uu____3915 =
               try
                 (fun uu___659_3938  ->
                    match () with
                    | () ->
                        let uu____3949 =
                          let uu____3958 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3958
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3949) ()
               with | uu___658_3969 -> fail "divide: not enough goals"  in
             bind uu____3915
               (fun uu____4006  ->
                  match uu____4006 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___641_4032 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___641_4032.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___641_4032.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___641_4032.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___641_4032.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___641_4032.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___641_4032.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___641_4032.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___641_4032.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___641_4032.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___641_4032.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___641_4032.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4033 = set lp  in
                      bind uu____4033
                        (fun uu____4041  ->
=======
             let uu____3920 =
               try
                 (fun uu___660_3943  ->
                    match () with
                    | () ->
                        let uu____3954 =
                          let uu____3963 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3963
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3954) ()
               with | uu___659_3974 -> fail "divide: not enough goals"  in
             bind uu____3920
               (fun uu____4011  ->
                  match uu____4011 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___642_4037 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___642_4037.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___642_4037.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___642_4037.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___642_4037.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___642_4037.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___642_4037.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___642_4037.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___642_4037.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___642_4037.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___642_4037.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4038 = set lp  in
                      bind uu____4038
                        (fun uu____4046  ->
>>>>>>> snap
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
<<<<<<< HEAD
                                       let uu___647_4057 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___647_4057.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___647_4057.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___647_4057.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___647_4057.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___647_4057.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___647_4057.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___647_4057.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___647_4057.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___647_4057.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___647_4057.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___647_4057.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4058 = set rp  in
                                     bind uu____4058
                                       (fun uu____4066  ->
=======
                                       let uu___648_4062 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___648_4062.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___648_4062.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___648_4062.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___648_4062.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___648_4062.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___648_4062.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___648_4062.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___648_4062.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___648_4062.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___648_4062.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4063 = set rp  in
                                     bind uu____4063
                                       (fun uu____4071  ->
>>>>>>> snap
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
<<<<<<< HEAD
                                                      let uu___653_4082 = rp'
=======
                                                      let uu___654_4087 = rp'
>>>>>>> snap
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
<<<<<<< HEAD
                                                          (uu___653_4082.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.all_implicits);
=======
                                                          (uu___654_4087.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.all_implicits);
>>>>>>> snap
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
<<<<<<< HEAD
                                                          (uu___653_4082.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___653_4082.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4083 = set p'
                                                       in
                                                    bind uu____4083
                                                      (fun uu____4091  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4097 
=======
                                                          (uu___654_4087.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___654_4087.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4088 = set p'
                                                       in
                                                    bind uu____4088
                                                      (fun uu____4096  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4102 
>>>>>>> snap
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
<<<<<<< HEAD
    let uu____4119 = divide FStar_BigInt.one f idtac  in
    bind uu____4119
      (fun uu____4132  -> match uu____4132 with | (a,()) -> ret a)
=======
    let uu____4124 = divide FStar_BigInt.one f idtac  in
    bind uu____4124
      (fun uu____4137  -> match uu____4137 with | (a,()) -> ret a)
>>>>>>> snap
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
<<<<<<< HEAD
         | uu____4170::uu____4171 ->
             let uu____4174 =
               let uu____4183 = map tau  in
               divide FStar_BigInt.one tau uu____4183  in
             bind uu____4174
               (fun uu____4201  ->
                  match uu____4201 with | (h,t) -> ret (h :: t)))
=======
         | uu____4175::uu____4176 ->
             let uu____4179 =
               let uu____4188 = map tau  in
               divide FStar_BigInt.one tau uu____4188  in
             bind uu____4179
               (fun uu____4206  ->
                  match uu____4206 with | (h,t) -> ret (h :: t)))
>>>>>>> snap
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
<<<<<<< HEAD
      let uu____4243 =
        bind t1
          (fun uu____4248  ->
             let uu____4249 = map t2  in
             bind uu____4249 (fun uu____4257  -> ret ()))
         in
      focus uu____4243
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4267  ->
    let uu____4270 =
      let uu____4273 = cur_goal ()  in
      bind uu____4273
        (fun goal  ->
           let uu____4282 =
             let uu____4289 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4289  in
           match uu____4282 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4298 =
                 let uu____4300 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4300  in
               if uu____4298
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4309 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4309 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4325 = new_uvar "intro" env' typ'  in
                  bind uu____4325
                    (fun uu____4342  ->
                       match uu____4342 with
=======
      let uu____4248 =
        bind t1
          (fun uu____4253  ->
             let uu____4254 = map t2  in
             bind uu____4254 (fun uu____4262  -> ret ()))
         in
      focus uu____4248
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4272  ->
    let uu____4275 =
      let uu____4278 = cur_goal ()  in
      bind uu____4278
        (fun goal  ->
           let uu____4287 =
             let uu____4294 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4294  in
           match uu____4287 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4303 =
                 let uu____4305 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4305  in
               if uu____4303
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4314 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4314 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4330 = new_uvar "intro" env' typ'  in
                  bind uu____4330
                    (fun uu____4347  ->
                       match uu____4347 with
>>>>>>> snap
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
<<<<<<< HEAD
                           let uu____4366 = set_solution goal sol  in
                           bind uu____4366
                             (fun uu____4372  ->
=======
                           let uu____4371 = set_solution goal sol  in
                           bind uu____4371
                             (fun uu____4377  ->
>>>>>>> snap
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
<<<<<<< HEAD
                                let uu____4374 =
                                  let uu____4377 = bnorm_goal g  in
                                  replace_cur uu____4377  in
                                bind uu____4374 (fun uu____4379  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4384 =
                 let uu____4386 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4387 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4386 uu____4387  in
               fail1 "goal is not an arrow (%s)" uu____4384)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4270
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4405  ->
    let uu____4412 = cur_goal ()  in
    bind uu____4412
=======
                                let uu____4379 =
                                  let uu____4382 = bnorm_goal g  in
                                  replace_cur uu____4382  in
                                bind uu____4379 (fun uu____4384  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4389 =
                 let uu____4391 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4392 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4391 uu____4392  in
               fail1 "goal is not an arrow (%s)" uu____4389)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4275
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4410  ->
    let uu____4417 = cur_goal ()  in
    bind uu____4417
>>>>>>> snap
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
<<<<<<< HEAD
         (let uu____4431 =
            let uu____4438 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4438  in
          match uu____4431 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4451 =
                let uu____4453 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4453  in
              if uu____4451
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4470 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4470
                    in
                 let bs =
                   let uu____4481 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4481; b]  in
                 let env' =
                   let uu____4507 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4507 bs  in
                 let uu____4508 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4508
                   (fun uu____4534  ->
                      match uu____4534 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4548 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4551 =
=======
         (let uu____4436 =
            let uu____4443 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4443  in
          match uu____4436 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4456 =
                let uu____4458 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4458  in
              if uu____4456
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4475 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4475
                    in
                 let bs =
                   let uu____4486 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4486; b]  in
                 let env' =
                   let uu____4512 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4512 bs  in
                 let uu____4513 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4513
                   (fun uu____4539  ->
                      match uu____4539 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4553 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4556 =
>>>>>>> snap
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
<<<<<<< HEAD
                              (FStar_Util.Inl bv) [] uu____4548
                              FStar_Parser_Const.effect_Tot_lid uu____4551 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4569 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4569 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4591 =
                                   let uu____4592 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4592.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4591
                                  in
                               let uu____4608 = set_solution goal tm  in
                               bind uu____4608
                                 (fun uu____4617  ->
                                    let uu____4618 =
                                      let uu____4621 =
                                        bnorm_goal
                                          (let uu___724_4624 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___724_4624.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___724_4624.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___724_4624.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___724_4624.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4621  in
                                    bind uu____4618
                                      (fun uu____4631  ->
                                         let uu____4632 =
                                           let uu____4637 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4637, b)  in
                                         ret uu____4632)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4646 =
                let uu____4648 = FStar_Tactics_Types.goal_env goal  in
                let uu____4649 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4648 uu____4649  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4646))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4669 = cur_goal ()  in
    bind uu____4669
      (fun goal  ->
         mlog
           (fun uu____4676  ->
              let uu____4677 =
                let uu____4679 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4679  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4677)
           (fun uu____4685  ->
              let steps =
                let uu____4689 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4689
                 in
              let t =
                let uu____4693 = FStar_Tactics_Types.goal_env goal  in
                let uu____4694 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4693 uu____4694  in
              let uu____4695 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4695))
=======
                              (FStar_Util.Inl bv) [] uu____4553
                              FStar_Parser_Const.effect_Tot_lid uu____4556 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4574 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4574 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4596 =
                                   let uu____4597 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4597.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4596
                                  in
                               let uu____4613 = set_solution goal tm  in
                               bind uu____4613
                                 (fun uu____4622  ->
                                    let uu____4623 =
                                      let uu____4626 =
                                        bnorm_goal
                                          (let uu___725_4629 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___725_4629.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___725_4629.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___725_4629.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___725_4629.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4626  in
                                    bind uu____4623
                                      (fun uu____4636  ->
                                         let uu____4637 =
                                           let uu____4642 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4642, b)  in
                                         ret uu____4637)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4651 =
                let uu____4653 = FStar_Tactics_Types.goal_env goal  in
                let uu____4654 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4653 uu____4654  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4651))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4674 = cur_goal ()  in
    bind uu____4674
      (fun goal  ->
         mlog
           (fun uu____4681  ->
              let uu____4682 =
                let uu____4684 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4684  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4682)
           (fun uu____4690  ->
              let steps =
                let uu____4694 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4694
                 in
              let t =
                let uu____4698 = FStar_Tactics_Types.goal_env goal  in
                let uu____4699 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4698 uu____4699  in
              let uu____4700 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4700))
>>>>>>> snap
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
<<<<<<< HEAD
        let uu____4720 =
=======
        let uu____4725 =
>>>>>>> snap
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
<<<<<<< HEAD
                 | g::uu____4728 -> g.FStar_Tactics_Types.opts
                 | uu____4731 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4736  ->
                    let uu____4737 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4737)
                 (fun uu____4742  ->
                    let uu____4743 = __tc_lax e t  in
                    bind uu____4743
                      (fun uu____4764  ->
                         match uu____4764 with
                         | (t1,uu____4774,uu____4775) ->
                             let steps =
                               let uu____4779 =
=======
                 | g::uu____4733 -> g.FStar_Tactics_Types.opts
                 | uu____4736 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4741  ->
                    let uu____4742 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4742)
                 (fun uu____4747  ->
                    let uu____4748 = __tc_lax e t  in
                    bind uu____4748
                      (fun uu____4769  ->
                         match uu____4769 with
                         | (t1,uu____4779,uu____4780) ->
                             let steps =
                               let uu____4784 =
>>>>>>> snap
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
<<<<<<< HEAD
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4779
=======
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4784
>>>>>>> snap
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
<<<<<<< HEAD
                               (fun uu____4785  ->
                                  let uu____4786 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4786)
                               (fun uu____4790  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4720
  
let (refine_intro : unit -> unit tac) =
  fun uu____4803  ->
    let uu____4806 =
      let uu____4809 = cur_goal ()  in
      bind uu____4809
        (fun g  ->
           let uu____4816 =
             let uu____4827 = FStar_Tactics_Types.goal_env g  in
             let uu____4828 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4827 uu____4828
              in
           match uu____4816 with
           | (uu____4831,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4857 =
                 let uu____4862 =
                   let uu____4867 =
                     let uu____4868 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4868]  in
                   FStar_Syntax_Subst.open_term uu____4867 phi  in
                 match uu____4862 with
                 | (bvs,phi1) ->
                     let uu____4893 =
                       let uu____4894 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4894  in
                     (uu____4893, phi1)
                  in
               (match uu____4857 with
                | (bv1,phi1) ->
                    let uu____4913 =
                      let uu____4916 = FStar_Tactics_Types.goal_env g  in
                      let uu____4917 =
                        let uu____4918 =
                          let uu____4921 =
                            let uu____4922 =
                              let uu____4929 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4929)  in
                            FStar_Syntax_Syntax.NT uu____4922  in
                          [uu____4921]  in
                        FStar_Syntax_Subst.subst uu____4918 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4916
                        uu____4917 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4913
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4938  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4806
=======
                               (fun uu____4790  ->
                                  let uu____4791 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4791)
                               (fun uu____4795  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4725
  
let (refine_intro : unit -> unit tac) =
  fun uu____4808  ->
    let uu____4811 =
      let uu____4814 = cur_goal ()  in
      bind uu____4814
        (fun g  ->
           let uu____4821 =
             let uu____4832 = FStar_Tactics_Types.goal_env g  in
             let uu____4833 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4832 uu____4833
              in
           match uu____4821 with
           | (uu____4836,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4862 =
                 let uu____4867 =
                   let uu____4872 =
                     let uu____4873 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4873]  in
                   FStar_Syntax_Subst.open_term uu____4872 phi  in
                 match uu____4867 with
                 | (bvs,phi1) ->
                     let uu____4898 =
                       let uu____4899 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4899  in
                     (uu____4898, phi1)
                  in
               (match uu____4862 with
                | (bv1,phi1) ->
                    let uu____4918 =
                      let uu____4921 = FStar_Tactics_Types.goal_env g  in
                      let uu____4922 =
                        let uu____4923 =
                          let uu____4926 =
                            let uu____4927 =
                              let uu____4934 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4934)  in
                            FStar_Syntax_Syntax.NT uu____4927  in
                          [uu____4926]  in
                        FStar_Syntax_Subst.subst uu____4923 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4921
                        uu____4922 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4918
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4943  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4811
>>>>>>> snap
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
<<<<<<< HEAD
      let uu____4961 = cur_goal ()  in
      bind uu____4961
=======
      let uu____4966 = cur_goal ()  in
      bind uu____4966
>>>>>>> snap
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
<<<<<<< HEAD
               let uu____4970 = FStar_Tactics_Types.goal_env goal  in
               let uu____4971 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4970 uu____4971
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4974 = __tc env t  in
           bind uu____4974
             (fun uu____4993  ->
                match uu____4993 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____5008  ->
                         let uu____5009 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5011 =
                           let uu____5013 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5013
=======
               let uu____4975 = FStar_Tactics_Types.goal_env goal  in
               let uu____4976 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4975 uu____4976
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4979 = __tc env t  in
           bind uu____4979
             (fun uu____4998  ->
                match uu____4998 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____5013  ->
                         let uu____5014 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5016 =
                           let uu____5018 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5018
>>>>>>> snap
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
<<<<<<< HEAD
                           uu____5009 uu____5011)
                      (fun uu____5017  ->
                         let uu____5018 =
                           let uu____5021 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5021 guard  in
                         bind uu____5018
                           (fun uu____5024  ->
                              mlog
                                (fun uu____5028  ->
                                   let uu____5029 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5031 =
                                     let uu____5033 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5033
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5029 uu____5031)
                                (fun uu____5037  ->
                                   let uu____5038 =
                                     let uu____5042 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5043 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5042 typ uu____5043  in
                                   bind uu____5038
=======
                           uu____5014 uu____5016)
                      (fun uu____5022  ->
                         let uu____5023 =
                           let uu____5026 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5026 guard  in
                         bind uu____5023
                           (fun uu____5029  ->
                              mlog
                                (fun uu____5033  ->
                                   let uu____5034 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5036 =
                                     let uu____5038 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5038
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5034 uu____5036)
                                (fun uu____5042  ->
                                   let uu____5043 =
                                     let uu____5047 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5048 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5047 typ uu____5048  in
                                   bind uu____5043
>>>>>>> snap
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
<<<<<<< HEAD
                                          (let uu____5053 =
                                             let uu____5055 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5055 t1  in
                                           let uu____5056 =
                                             let uu____5058 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5058 typ  in
                                           let uu____5059 =
                                             let uu____5061 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5062 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____5061 uu____5062  in
                                           let uu____5063 =
                                             let uu____5065 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5066 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____5065 uu____5066  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____5053 uu____5056 uu____5059
                                             uu____5063)))))))
=======
                                          (let uu____5058 =
                                             let uu____5060 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5060 t1  in
                                           let uu____5061 =
                                             let uu____5063 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5063 typ  in
                                           let uu____5064 =
                                             let uu____5066 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5067 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____5066 uu____5067  in
                                           let uu____5068 =
                                             let uu____5070 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5071 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____5070 uu____5071  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____5058 uu____5061 uu____5064
                                             uu____5068)))))))
>>>>>>> snap
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
<<<<<<< HEAD
        let uu____5092 =
          mlog
            (fun uu____5097  ->
               let uu____5098 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5098)
            (fun uu____5103  ->
               let uu____5104 =
                 let uu____5111 = __exact_now set_expected_typ1 tm  in
                 catch uu____5111  in
               bind uu____5104
                 (fun uu___2_5120  ->
                    match uu___2_5120 with
=======
        let uu____5097 =
          mlog
            (fun uu____5102  ->
               let uu____5103 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5103)
            (fun uu____5108  ->
               let uu____5109 =
                 let uu____5116 = __exact_now set_expected_typ1 tm  in
                 catch uu____5116  in
               bind uu____5109
                 (fun uu___2_5125  ->
                    match uu___2_5125 with
>>>>>>> snap
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
<<<<<<< HEAD
                          (fun uu____5131  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5135  ->
                             let uu____5136 =
                               let uu____5143 =
                                 let uu____5146 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5146
                                   (fun uu____5151  ->
                                      let uu____5152 = refine_intro ()  in
                                      bind uu____5152
                                        (fun uu____5156  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5143  in
                             bind uu____5136
                               (fun uu___1_5163  ->
                                  match uu___1_5163 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5172  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5175  -> ret ())
                                  | FStar_Util.Inl uu____5176 ->
                                      mlog
                                        (fun uu____5178  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5181  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5092
=======
                          (fun uu____5136  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5140  ->
                             let uu____5141 =
                               let uu____5148 =
                                 let uu____5151 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5151
                                   (fun uu____5156  ->
                                      let uu____5157 = refine_intro ()  in
                                      bind uu____5157
                                        (fun uu____5161  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5148  in
                             bind uu____5141
                               (fun uu___1_5168  ->
                                  match uu___1_5168 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5177  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5180  -> ret ())
                                  | FStar_Util.Inl uu____5181 ->
                                      mlog
                                        (fun uu____5183  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5186  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5097
>>>>>>> snap
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
<<<<<<< HEAD
          let uu____5233 = f x  in
          bind uu____5233
            (fun y  ->
               let uu____5241 = mapM f xs  in
               bind uu____5241 (fun ys  -> ret (y :: ys)))
=======
          let uu____5238 = f x  in
          bind uu____5238
            (fun y  ->
               let uu____5246 = mapM f xs  in
               bind uu____5246 (fun ys  -> ret (y :: ys)))
>>>>>>> snap
  
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
<<<<<<< HEAD
            let uu____5351 = f e ty2 ty1  in
            bind uu____5351
              (fun uu___3_5365  ->
                 if uu___3_5365
                 then ret acc
                 else
                   (let uu____5385 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5385 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5406 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5408 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5406
                          uu____5408
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5425 =
                          let uu____5427 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5427  in
                        if uu____5425
                        then fail "Codomain is effectful"
                        else
                          (let uu____5451 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5451
                             (fun uu____5478  ->
                                match uu____5478 with
=======
            let uu____5356 = f e ty2 ty1  in
            bind uu____5356
              (fun uu___3_5370  ->
                 if uu___3_5370
                 then ret acc
                 else
                   (let uu____5390 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5390 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5411 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5413 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5411
                          uu____5413
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5430 =
                          let uu____5432 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5432  in
                        if uu____5430
                        then fail "Codomain is effectful"
                        else
                          (let uu____5456 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5456
                             (fun uu____5483  ->
                                match uu____5483 with
>>>>>>> snap
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
<<<<<<< HEAD
        let uu____5584 =
          mlog
            (fun uu____5589  ->
               let uu____5590 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5590)
            (fun uu____5595  ->
               let uu____5596 = cur_goal ()  in
               bind uu____5596
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5604 = __tc e tm  in
                    bind uu____5604
                      (fun uu____5625  ->
                         match uu____5625 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5638 =
                               let uu____5649 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5649
                                in
                             bind uu____5638
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5670  ->
                                       let uu____5671 =
                                         FStar_Common.string_of_list
                                           (fun uu____5683  ->
                                              match uu____5683 with
                                              | (t,uu____5692,uu____5693) ->
=======
        let uu____5589 =
          mlog
            (fun uu____5594  ->
               let uu____5595 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5595)
            (fun uu____5600  ->
               let uu____5601 = cur_goal ()  in
               bind uu____5601
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5609 = __tc e tm  in
                    bind uu____5609
                      (fun uu____5630  ->
                         match uu____5630 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5643 =
                               let uu____5654 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5654
                                in
                             bind uu____5643
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5675  ->
                                       let uu____5676 =
                                         FStar_Common.string_of_list
                                           (fun uu____5688  ->
                                              match uu____5688 with
                                              | (t,uu____5697,uu____5698) ->
>>>>>>> snap
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
<<<<<<< HEAD
                                         uu____5671)
                                    (fun uu____5701  ->
=======
                                         uu____5676)
                                    (fun uu____5706  ->
>>>>>>> snap
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
<<<<<<< HEAD
                                             uu____5716) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5720 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5743  ->
                                              fun w  ->
                                                match uu____5743 with
                                                | (uvt,q,uu____5761) ->
=======
                                             uu____5721) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5725 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5748  ->
                                              fun w  ->
                                                match uu____5748 with
                                                | (uvt,q,uu____5766) ->
>>>>>>> snap
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
<<<<<<< HEAD
                                         let uu____5793 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5810  ->
                                              fun s  ->
                                                match uu____5810 with
                                                | (uu____5822,uu____5823,uv)
                                                    ->
                                                    let uu____5825 =
=======
                                         let uu____5798 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5815  ->
                                              fun s  ->
                                                match uu____5815 with
                                                | (uu____5827,uu____5828,uv)
                                                    ->
                                                    let uu____5830 =
>>>>>>> snap
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
<<<<<<< HEAD
                                                      uu____5825) uvs
                                           uu____5793
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5835 = solve' goal w  in
                                       bind uu____5835
                                         (fun uu____5840  ->
                                            let uu____5841 =
                                              mapM
                                                (fun uu____5858  ->
                                                   match uu____5858 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5870 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5870 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5875 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5876 =
=======
                                                      uu____5830) uvs
                                           uu____5798
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5840 = solve' goal w  in
                                       bind uu____5840
                                         (fun uu____5845  ->
                                            let uu____5846 =
                                              mapM
                                                (fun uu____5863  ->
                                                   match uu____5863 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5875 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5875 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5880 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5881 =
>>>>>>> snap
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
<<<<<<< HEAD
                                                            if uu____5876
                                                            then ret ()
                                                            else
                                                              (let uu____5883
                                                                 =
                                                                 let uu____5886
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___891_5889
=======
                                                            if uu____5881
                                                            then ret ()
                                                            else
                                                              (let uu____5888
                                                                 =
                                                                 let uu____5891
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___892_5894
>>>>>>> snap
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
<<<<<<< HEAD
                                                                    (uu___891_5889.FStar_Tactics_Types.goal_main_env);
=======
                                                                    (uu___892_5894.FStar_Tactics_Types.goal_main_env);
>>>>>>> snap
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
<<<<<<< HEAD
                                                                    (uu___891_5889.FStar_Tactics_Types.opts);
=======
                                                                    (uu___892_5894.FStar_Tactics_Types.opts);
>>>>>>> snap
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
<<<<<<< HEAD
                                                                    (uu___891_5889.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5886]
                                                                  in
                                                               add_goals
                                                                 uu____5883)))
                                                uvs
                                               in
                                            bind uu____5841
                                              (fun uu____5894  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5584
=======
                                                                    (uu___892_5894.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5891]
                                                                  in
                                                               add_goals
                                                                 uu____5888)))
                                                uvs
                                               in
                                            bind uu____5846
                                              (fun uu____5899  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5589
>>>>>>> snap
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
<<<<<<< HEAD
    let uu____5922 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5922
    then
      let uu____5931 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5946 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5999 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5931 with
      | (pre,post) ->
          let post1 =
            let uu____6032 =
              let uu____6043 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6043]  in
            FStar_Syntax_Util.mk_app post uu____6032  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6074 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6074
       then
         let uu____6083 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6083
=======
    let uu____5927 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5927
    then
      let uu____5936 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5951 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____6004 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5936 with
      | (pre,post) ->
          let post1 =
            let uu____6037 =
              let uu____6048 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6048]  in
            FStar_Syntax_Util.mk_app post uu____6037  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6079 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6079
       then
         let uu____6088 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6088
>>>>>>> snap
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
<<<<<<< HEAD
            let uu____6162 = f x e  in
            bind uu____6162 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6177 =
      let uu____6180 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6187  ->
                  let uu____6188 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6188)
               (fun uu____6194  ->
                  let is_unit_t t =
                    let uu____6202 =
                      let uu____6203 = FStar_Syntax_Subst.compress t  in
                      uu____6203.FStar_Syntax_Syntax.n  in
                    match uu____6202 with
=======
            let uu____6167 = f x e  in
            bind uu____6167 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6182 =
      let uu____6185 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6192  ->
                  let uu____6193 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6193)
               (fun uu____6199  ->
                  let is_unit_t t =
                    let uu____6207 =
                      let uu____6208 = FStar_Syntax_Subst.compress t  in
                      uu____6208.FStar_Syntax_Syntax.n  in
                    match uu____6207 with
>>>>>>> snap
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
<<<<<<< HEAD
                    | uu____6209 -> false  in
                  let uu____6211 = cur_goal ()  in
                  bind uu____6211
                    (fun goal  ->
                       let uu____6217 =
                         let uu____6226 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6226 tm  in
                       bind uu____6217
                         (fun uu____6241  ->
                            match uu____6241 with
                            | (tm1,t,guard) ->
                                let uu____6253 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6253 with
                                 | (bs,comp) ->
                                     let uu____6286 = lemma_or_sq comp  in
                                     (match uu____6286 with
=======
                    | uu____6214 -> false  in
                  let uu____6216 = cur_goal ()  in
                  bind uu____6216
                    (fun goal  ->
                       let uu____6222 =
                         let uu____6231 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6231 tm  in
                       bind uu____6222
                         (fun uu____6246  ->
                            match uu____6246 with
                            | (tm1,t,guard) ->
                                let uu____6258 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6258 with
                                 | (bs,comp) ->
                                     let uu____6291 = lemma_or_sq comp  in
                                     (match uu____6291 with
>>>>>>> snap
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
<<<<<<< HEAD
                                          let uu____6306 =
                                            fold_left
                                              (fun uu____6368  ->
                                                 fun uu____6369  ->
                                                   match (uu____6368,
                                                           uu____6369)
=======
                                          let uu____6311 =
                                            fold_left
                                              (fun uu____6373  ->
                                                 fun uu____6374  ->
                                                   match (uu____6373,
                                                           uu____6374)
>>>>>>> snap
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
<<<<<<< HEAD
                                                       let uu____6520 =
                                                         is_unit_t b_t  in
                                                       if uu____6520
=======
                                                       let uu____6525 =
                                                         is_unit_t b_t  in
                                                       if uu____6525
>>>>>>> snap
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
<<<<<<< HEAD
                                                         (let uu____6643 =
                                                            let uu____6650 =
=======
                                                         (let uu____6648 =
                                                            let uu____6655 =
>>>>>>> snap
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
<<<<<<< HEAD
                                                              uu____6650 b_t
                                                             in
                                                          bind uu____6643
                                                            (fun uu____6681 
                                                               ->
                                                               match uu____6681
=======
                                                              uu____6655 b_t
                                                             in
                                                          bind uu____6648
                                                            (fun uu____6686 
                                                               ->
                                                               match uu____6686
>>>>>>> snap
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
<<<<<<< HEAD
                                          bind uu____6306
                                            (fun uu____6867  ->
                                               match uu____6867 with
=======
                                          bind uu____6311
                                            (fun uu____6872  ->
                                               match uu____6872 with
>>>>>>> snap
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
<<<<<<< HEAD
                                                   let uu____6955 =
                                                     let uu____6959 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6960 =
=======
                                                   let uu____6960 =
                                                     let uu____6964 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6965 =
>>>>>>> snap
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
<<<<<<< HEAD
                                                     let uu____6961 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6959
                                                       uu____6960 uu____6961
                                                      in
                                                   bind uu____6955
=======
                                                     let uu____6966 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6964
                                                       uu____6965 uu____6966
                                                      in
                                                   bind uu____6960
>>>>>>> snap
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
<<<<<<< HEAD
                                                          let uu____6972 =
                                                            let uu____6974 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6974
                                                              tm1
                                                             in
                                                          let uu____6975 =
                                                            let uu____6977 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6978 =
=======
                                                          let uu____6977 =
                                                            let uu____6979 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6979
                                                              tm1
                                                             in
                                                          let uu____6980 =
                                                            let uu____6982 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6983 =
>>>>>>> snap
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
<<<<<<< HEAD
                                                            tts uu____6977
                                                              uu____6978
                                                             in
                                                          let uu____6979 =
                                                            let uu____6981 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6982 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6981
                                                              uu____6982
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6972
                                                            uu____6975
                                                            uu____6979
                                                        else
                                                          (let uu____6986 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6986
                                                             (fun uu____6994 
=======
                                                            tts uu____6982
                                                              uu____6983
                                                             in
                                                          let uu____6984 =
                                                            let uu____6986 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6987 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6986
                                                              uu____6987
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6977
                                                            uu____6980
                                                            uu____6984
                                                        else
                                                          (let uu____6991 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6991
                                                             (fun uu____6999 
>>>>>>> snap
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
<<<<<<< HEAD
                                                                    let uu____7020
                                                                    =
                                                                    let uu____7023
=======
                                                                    let uu____7025
                                                                    =
                                                                    let uu____7028
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
<<<<<<< HEAD
                                                                    uu____7023
=======
                                                                    uu____7028
>>>>>>> snap
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
<<<<<<< HEAD
                                                                    uu____7020
=======
                                                                    uu____7025
>>>>>>> snap
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
<<<<<<< HEAD
                                                                    let uu____7059
=======
                                                                    let uu____7064
>>>>>>> snap
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
<<<<<<< HEAD
                                                                    uu____7059)
=======
                                                                    uu____7064)
>>>>>>> snap
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
<<<<<<< HEAD
                                                                  let uu____7076
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7076
                                                                  with
                                                                  | (hd1,uu____7095)
=======
                                                                  let uu____7081
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7081
                                                                  with
                                                                  | (hd1,uu____7100)
>>>>>>> snap
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
<<<<<<< HEAD
                                                                    (uv,uu____7122)
=======
                                                                    (uv,uu____7127)
>>>>>>> snap
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
<<<<<<< HEAD
                                                                    uu____7139
                                                                    -> false)
                                                                   in
                                                                let uu____7141
=======
                                                                    uu____7144
                                                                    -> false)
                                                                   in
                                                                let uu____7146
>>>>>>> snap
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
<<<<<<< HEAD
                                                                    let uu____7184
                                                                    = imp  in
                                                                    match uu____7184
=======
                                                                    let uu____7189
                                                                    = imp  in
                                                                    match uu____7189
>>>>>>> snap
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____7195
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7195
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7217)
                                                                    ->
                                                                    let uu____7242
                                                                    =
                                                                    let uu____7243
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7243.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7242
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7251)
=======
                                                                    let uu____7200
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7200
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7222)
                                                                    ->
                                                                    let uu____7247
                                                                    =
                                                                    let uu____7248
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7248.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7247
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7256)
>>>>>>> snap
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
<<<<<<< HEAD
                                                                    (let uu___1006_7271
=======
                                                                    (let uu___1007_7276
>>>>>>> snap
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1006_7271.FStar_Tactics_Types.goal_main_env);
=======
                                                                    (uu___1007_7276.FStar_Tactics_Types.goal_main_env);
>>>>>>> snap
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1006_7271.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1006_7271.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1006_7271.FStar_Tactics_Types.label)
=======
                                                                    (uu___1007_7276.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1007_7276.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1007_7276.FStar_Tactics_Types.label)
>>>>>>> snap
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
<<<<<<< HEAD
                                                                    uu____7274
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7280
                                                                     ->
                                                                    let uu____7281
=======
                                                                    uu____7279
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7285
                                                                     ->
                                                                    let uu____7286
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
<<<<<<< HEAD
                                                                    let uu____7283
=======
                                                                    let uu____7288
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
<<<<<<< HEAD
                                                                    uu____7281
                                                                    uu____7283)
                                                                    (fun
                                                                    uu____7290
                                                                     ->
                                                                    let env =
                                                                    let uu___1011_7292
=======
                                                                    uu____7286
                                                                    uu____7288)
                                                                    (fun
                                                                    uu____7295
                                                                     ->
                                                                    let env =
                                                                    let uu___1012_7297
>>>>>>> snap
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.curmodule);
=======
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.curmodule);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.is_pattern);
=======
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.attrtab);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1011_7292.FStar_TypeChecker_Env.strict_args_tab)
=======
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1012_7297.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
<<<<<<< HEAD
                                                                    let uu____7295
                                                                    =
                                                                    let uu____7298
=======
                                                                    let uu____7300
                                                                    =
                                                                    let uu____7303
>>>>>>> snap
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
<<<<<<< HEAD
                                                                    let uu____7302
=======
                                                                    let uu____7307
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
<<<<<<< HEAD
                                                                    let uu____7304
=======
                                                                    let uu____7309
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
<<<<<<< HEAD
                                                                    uu____7302
                                                                    uu____7304
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7310
=======
                                                                    uu____7307
                                                                    uu____7309
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7315
>>>>>>> snap
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
<<<<<<< HEAD
                                                                    uu____7298
                                                                    uu____7310
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7295
                                                                    (fun
                                                                    uu____7314
=======
                                                                    uu____7303
                                                                    uu____7315
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7300
                                                                    (fun
                                                                    uu____7319
>>>>>>> snap
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
<<<<<<< HEAD
                                                                  uu____7141
=======
                                                                  uu____7146
>>>>>>> snap
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
<<<<<<< HEAD
                                                                    let uu____7378
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7378
                                                                    then
                                                                    let uu____7383
=======
                                                                    let uu____7383
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7383
                                                                    then
                                                                    let uu____7388
>>>>>>> snap
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
<<<<<<< HEAD
                                                                    uu____7383
=======
                                                                    uu____7388
>>>>>>> snap
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
<<<<<<< HEAD
                                                                    let uu____7398
                                                                    =
                                                                    let uu____7400
=======
                                                                    let uu____7403
                                                                    =
                                                                    let uu____7405
>>>>>>> snap
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
<<<<<<< HEAD
                                                                    uu____7400
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7398)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7401
                                                                    =
                                                                    let uu____7404
=======
                                                                    uu____7405
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7403)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7406
                                                                    =
                                                                    let uu____7409
>>>>>>> snap
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
<<<<<<< HEAD
                                                                    uu____7404
                                                                    guard  in
                                                                    bind
                                                                    uu____7401
                                                                    (fun
                                                                    uu____7408
                                                                     ->
                                                                    let uu____7409
                                                                    =
                                                                    let uu____7412
                                                                    =
                                                                    let uu____7414
                                                                    =
                                                                    let uu____7416
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7417
=======
                                                                    uu____7409
                                                                    guard  in
                                                                    bind
                                                                    uu____7406
                                                                    (fun
                                                                    uu____7413
                                                                     ->
                                                                    let uu____7414
                                                                    =
                                                                    let uu____7417
                                                                    =
                                                                    let uu____7419
                                                                    =
                                                                    let uu____7421
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7422
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
<<<<<<< HEAD
                                                                    uu____7416
                                                                    uu____7417
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7414
                                                                     in
                                                                    if
                                                                    uu____7412
                                                                    then
                                                                    let uu____7421
=======
                                                                    uu____7421
                                                                    uu____7422
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7419
                                                                     in
                                                                    if
                                                                    uu____7417
                                                                    then
                                                                    let uu____7426
>>>>>>> snap
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
<<<<<<< HEAD
                                                                    uu____7421
=======
                                                                    uu____7426
>>>>>>> snap
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
<<<<<<< HEAD
                                                                    uu____7409
                                                                    (fun
                                                                    uu____7426
=======
                                                                    uu____7414
                                                                    (fun
                                                                    uu____7431
>>>>>>> snap
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
<<<<<<< HEAD
      focus uu____6180  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6177
=======
      focus uu____6185  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6182
>>>>>>> snap
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
<<<<<<< HEAD
    let uu____7450 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7450 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7460::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
=======
    let uu____7455 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7455 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7465::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
>>>>>>> snap
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
<<<<<<< HEAD
        (l,uu____7520::uu____7521::(e1,uu____7523)::(e2,uu____7525)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7602 ->
        let uu____7605 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7605 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7619 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7619 with
              | (hd1,args) ->
                  let uu____7668 =
                    let uu____7683 =
                      let uu____7684 = FStar_Syntax_Subst.compress hd1  in
                      uu____7684.FStar_Syntax_Syntax.n  in
                    (uu____7683, args)  in
                  (match uu____7668 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7704,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7705))::
=======
        (l,uu____7525::uu____7526::(e1,uu____7528)::(e2,uu____7530)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7607 ->
        let uu____7610 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7610 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7624 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7624 with
              | (hd1,args) ->
                  let uu____7673 =
                    let uu____7688 =
                      let uu____7689 = FStar_Syntax_Subst.compress hd1  in
                      uu____7689.FStar_Syntax_Syntax.n  in
                    (uu____7688, args)  in
                  (match uu____7673 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7709,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7710))::
>>>>>>> snap
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
<<<<<<< HEAD
                   | uu____7773 -> FStar_Pervasives_Native.None)))
=======
                   | uu____7778 -> FStar_Pervasives_Native.None)))
>>>>>>> snap
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
<<<<<<< HEAD
    let uu____7810 = destruct_eq' typ  in
    match uu____7810 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7840 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7840 with
=======
    let uu____7815 = destruct_eq' typ  in
    match uu____7815 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7845 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7845 with
>>>>>>> snap
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
<<<<<<< HEAD
        let uu____7909 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7909 with
=======
        let uu____7914 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7914 with
>>>>>>> snap
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
<<<<<<< HEAD
              (let uu____7967 = aux e'  in
               FStar_Util.map_opt uu____7967
                 (fun uu____7998  ->
                    match uu____7998 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8024 = aux e  in
      FStar_Util.map_opt uu____8024
        (fun uu____8055  ->
           match uu____8055 with
=======
              (let uu____7972 = aux e'  in
               FStar_Util.map_opt uu____7972
                 (fun uu____8003  ->
                    match uu____8003 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8029 = aux e  in
      FStar_Util.map_opt uu____8029
        (fun uu____8060  ->
           match uu____8060 with
>>>>>>> snap
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
<<<<<<< HEAD
          let uu____8129 =
            let uu____8140 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8140  in
          FStar_Util.map_opt uu____8129
            (fun uu____8158  ->
               match uu____8158 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1119_8180 = bv  in
                     let uu____8181 =
=======
          let uu____8134 =
            let uu____8145 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8145  in
          FStar_Util.map_opt uu____8134
            (fun uu____8163  ->
               match uu____8163 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1120_8185 = bv  in
                     let uu____8186 =
>>>>>>> snap
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                         (uu___1119_8180.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1119_8180.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____8181
=======
                         (uu___1120_8185.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1120_8185.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____8186
>>>>>>> snap
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
<<<<<<< HEAD
                     let uu___1123_8189 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____8190 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____8199 =
                       let uu____8202 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____8202  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1123_8189.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____8190;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____8199;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1123_8189.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1123_8189.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1123_8189.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1123_8189.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1126_8203 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1126_8203.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1126_8203.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1126_8203.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1126_8203.FStar_Tactics_Types.label)
=======
                     let uu___1124_8194 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____8195 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____8204 =
                       let uu____8207 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____8207  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1124_8194.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____8195;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____8204;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1124_8194.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1124_8194.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1124_8194.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1124_8194.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1127_8208 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1127_8208.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1127_8208.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1127_8208.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1127_8208.FStar_Tactics_Types.label)
>>>>>>> snap
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
<<<<<<< HEAD
    let uu____8214 =
      let uu____8217 = cur_goal ()  in
      bind uu____8217
        (fun goal  ->
           let uu____8225 = h  in
           match uu____8225 with
           | (bv,uu____8229) ->
               mlog
                 (fun uu____8237  ->
                    let uu____8238 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8240 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8238
                      uu____8240)
                 (fun uu____8245  ->
                    let uu____8246 =
                      let uu____8257 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8257  in
                    match uu____8246 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8284 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8284 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8299 =
                               let uu____8300 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8300.FStar_Syntax_Syntax.n  in
                             (match uu____8299 with
=======
    let uu____8219 =
      let uu____8222 = cur_goal ()  in
      bind uu____8222
        (fun goal  ->
           let uu____8230 = h  in
           match uu____8230 with
           | (bv,uu____8234) ->
               mlog
                 (fun uu____8242  ->
                    let uu____8243 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8245 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8243
                      uu____8245)
                 (fun uu____8250  ->
                    let uu____8251 =
                      let uu____8262 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8262  in
                    match uu____8251 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8289 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8289 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8304 =
                               let uu____8305 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8305.FStar_Syntax_Syntax.n  in
                             (match uu____8304 with
>>>>>>> snap
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
<<<<<<< HEAD
                                    let uu___1149_8317 = bv2  in
                                    let uu____8318 =
=======
                                    let uu___1150_8322 = bv2  in
                                    let uu____8323 =
>>>>>>> snap
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                        (uu___1149_8317.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1149_8317.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8318
=======
                                        (uu___1150_8322.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1150_8322.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8323
>>>>>>> snap
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
<<<<<<< HEAD
                                    let uu___1153_8326 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8327 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8336 =
                                      let uu____8339 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8339
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1153_8326.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8327;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8336;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1153_8326.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1153_8326.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1153_8326.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1153_8326.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1156_8342 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1156_8342.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1156_8342.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1156_8342.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1156_8342.FStar_Tactics_Types.label)
                                     })
                              | uu____8343 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8345 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8214
=======
                                    let uu___1154_8331 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8332 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8341 =
                                      let uu____8344 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8344
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1154_8331.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8332;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8341;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1154_8331.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1154_8331.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1154_8331.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1154_8331.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1157_8347 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1157_8347.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1157_8347.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1157_8347.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1157_8347.FStar_Tactics_Types.label)
                                     })
                              | uu____8348 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8350 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8219
>>>>>>> snap
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
<<<<<<< HEAD
      let uu____8375 =
        let uu____8378 = cur_goal ()  in
        bind uu____8378
          (fun goal  ->
             let uu____8389 = b  in
             match uu____8389 with
             | (bv,uu____8393) ->
                 let bv' =
                   let uu____8399 =
                     let uu___1167_8400 = bv  in
                     let uu____8401 =
=======
      let uu____8380 =
        let uu____8383 = cur_goal ()  in
        bind uu____8383
          (fun goal  ->
             let uu____8394 = b  in
             match uu____8394 with
             | (bv,uu____8398) ->
                 let bv' =
                   let uu____8404 =
                     let uu___1168_8405 = bv  in
                     let uu____8406 =
>>>>>>> snap
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
<<<<<<< HEAD
                       FStar_Syntax_Syntax.ppname = uu____8401;
                       FStar_Syntax_Syntax.index =
                         (uu___1167_8400.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1167_8400.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8399  in
                 let s1 =
                   let uu____8406 =
                     let uu____8407 =
                       let uu____8414 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8414)  in
                     FStar_Syntax_Syntax.NT uu____8407  in
                   [uu____8406]  in
                 let uu____8419 = subst_goal bv bv' s1 goal  in
                 (match uu____8419 with
=======
                       FStar_Syntax_Syntax.ppname = uu____8406;
                       FStar_Syntax_Syntax.index =
                         (uu___1168_8405.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1168_8405.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8404  in
                 let s1 =
                   let uu____8411 =
                     let uu____8412 =
                       let uu____8419 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8419)  in
                     FStar_Syntax_Syntax.NT uu____8412  in
                   [uu____8411]  in
                 let uu____8424 = subst_goal bv bv' s1 goal  in
                 (match uu____8424 with
>>>>>>> snap
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
<<<<<<< HEAD
      FStar_All.pipe_left (wrap_err "rename_to") uu____8375
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8441 =
      let uu____8444 = cur_goal ()  in
      bind uu____8444
        (fun goal  ->
           let uu____8453 = b  in
           match uu____8453 with
           | (bv,uu____8457) ->
               let uu____8462 =
                 let uu____8473 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8473  in
               (match uu____8462 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8500 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8500 with
                     | (ty,u) ->
                         let uu____8509 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8509
                           (fun uu____8528  ->
                              match uu____8528 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1191_8538 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1191_8538.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1191_8538.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8542 =
                                      let uu____8543 =
                                        let uu____8550 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8550)  in
                                      FStar_Syntax_Syntax.NT uu____8543  in
                                    [uu____8542]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1196_8562 = b1  in
                                         let uu____8563 =
=======
      FStar_All.pipe_left (wrap_err "rename_to") uu____8380
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8446 =
      let uu____8449 = cur_goal ()  in
      bind uu____8449
        (fun goal  ->
           let uu____8458 = b  in
           match uu____8458 with
           | (bv,uu____8462) ->
               let uu____8467 =
                 let uu____8478 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8478  in
               (match uu____8467 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8505 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8505 with
                     | (ty,u) ->
                         let uu____8514 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8514
                           (fun uu____8533  ->
                              match uu____8533 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1192_8543 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1192_8543.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1192_8543.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8547 =
                                      let uu____8548 =
                                        let uu____8555 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8555)  in
                                      FStar_Syntax_Syntax.NT uu____8548  in
                                    [uu____8547]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1197_8567 = b1  in
                                         let uu____8568 =
>>>>>>> snap
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                             (uu___1196_8562.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1196_8562.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8563
=======
                                             (uu___1197_8567.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1197_8567.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8568
>>>>>>> snap
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
<<<<<<< HEAD
                                    (fun uu____8570  ->
                                       let new_goal =
                                         let uu____8572 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8573 =
                                           let uu____8574 =
=======
                                    (fun uu____8575  ->
                                       let new_goal =
                                         let uu____8577 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8578 =
                                           let uu____8579 =
>>>>>>> snap
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
<<<<<<< HEAD
                                             uu____8574
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8572 uu____8573
                                          in
                                       let uu____8575 = add_goals [new_goal]
                                          in
                                       bind uu____8575
                                         (fun uu____8580  ->
                                            let uu____8581 =
=======
                                             uu____8579
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8577 uu____8578
                                          in
                                       let uu____8580 = add_goals [new_goal]
                                          in
                                       bind uu____8580
                                         (fun uu____8585  ->
                                            let uu____8586 =
>>>>>>> snap
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
<<<<<<< HEAD
                                              uu____8581
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8441
=======
                                              uu____8586
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8446
>>>>>>> snap
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
<<<<<<< HEAD
      let uu____8607 =
        let uu____8610 = cur_goal ()  in
        bind uu____8610
          (fun goal  ->
             let uu____8619 = b  in
             match uu____8619 with
             | (bv,uu____8623) ->
                 let uu____8628 =
                   let uu____8639 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8639  in
                 (match uu____8628 with
=======
      let uu____8612 =
        let uu____8615 = cur_goal ()  in
        bind uu____8615
          (fun goal  ->
             let uu____8624 = b  in
             match uu____8624 with
             | (bv,uu____8628) ->
                 let uu____8633 =
                   let uu____8644 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8644  in
                 (match uu____8633 with
>>>>>>> snap
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
<<<<<<< HEAD
                        let uu____8669 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8669
=======
                        let uu____8674 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8674
>>>>>>> snap
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
<<<<<<< HEAD
                        let uu___1217_8674 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1217_8674.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1217_8674.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8676 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8676))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8607
  
let (revert : unit -> unit tac) =
  fun uu____8689  ->
    let uu____8692 = cur_goal ()  in
    bind uu____8692
      (fun goal  ->
         let uu____8698 =
           let uu____8705 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8705  in
         match uu____8698 with
=======
                        let uu___1218_8679 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1218_8679.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1218_8679.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8681 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8681))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8612
  
let (revert : unit -> unit tac) =
  fun uu____8694  ->
    let uu____8697 = cur_goal ()  in
    bind uu____8697
      (fun goal  ->
         let uu____8703 =
           let uu____8710 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8710  in
         match uu____8703 with
>>>>>>> snap
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
<<<<<<< HEAD
               let uu____8722 =
                 let uu____8725 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8725  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8722
                in
             let uu____8740 = new_uvar "revert" env' typ'  in
             bind uu____8740
               (fun uu____8756  ->
                  match uu____8756 with
                  | (r,u_r) ->
                      let uu____8765 =
                        let uu____8768 =
                          let uu____8769 =
                            let uu____8770 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8770.FStar_Syntax_Syntax.pos  in
                          let uu____8773 =
                            let uu____8778 =
                              let uu____8779 =
                                let uu____8788 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8788  in
                              [uu____8779]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8778  in
                          uu____8773 FStar_Pervasives_Native.None uu____8769
                           in
                        set_solution goal uu____8768  in
                      bind uu____8765
                        (fun uu____8807  ->
=======
               let uu____8727 =
                 let uu____8730 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8730  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8727
                in
             let uu____8745 = new_uvar "revert" env' typ'  in
             bind uu____8745
               (fun uu____8761  ->
                  match uu____8761 with
                  | (r,u_r) ->
                      let uu____8770 =
                        let uu____8773 =
                          let uu____8774 =
                            let uu____8775 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8775.FStar_Syntax_Syntax.pos  in
                          let uu____8778 =
                            let uu____8783 =
                              let uu____8784 =
                                let uu____8793 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8793  in
                              [uu____8784]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8783  in
                          uu____8778 FStar_Pervasives_Native.None uu____8774
                           in
                        set_solution goal uu____8773  in
                      bind uu____8770
                        (fun uu____8812  ->
>>>>>>> snap
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
<<<<<<< HEAD
      let uu____8821 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8821
=======
      let uu____8826 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8826
>>>>>>> snap
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
<<<<<<< HEAD
    let uu____8837 = cur_goal ()  in
    bind uu____8837
      (fun goal  ->
         mlog
           (fun uu____8845  ->
              let uu____8846 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8848 =
                let uu____8850 =
                  let uu____8852 =
                    let uu____8861 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8861  in
                  FStar_All.pipe_right uu____8852 FStar_List.length  in
                FStar_All.pipe_right uu____8850 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8846 uu____8848)
           (fun uu____8882  ->
              let uu____8883 =
                let uu____8894 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8894  in
              match uu____8883 with
=======
    let uu____8842 = cur_goal ()  in
    bind uu____8842
      (fun goal  ->
         mlog
           (fun uu____8850  ->
              let uu____8851 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8853 =
                let uu____8855 =
                  let uu____8857 =
                    let uu____8866 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8866  in
                  FStar_All.pipe_right uu____8857 FStar_List.length  in
                FStar_All.pipe_right uu____8855 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8851 uu____8853)
           (fun uu____8887  ->
              let uu____8888 =
                let uu____8899 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8899  in
              match uu____8888 with
>>>>>>> snap
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
<<<<<<< HEAD
                        let uu____8939 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8939
                        then
                          let uu____8944 =
                            let uu____8946 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8946
                             in
                          fail uu____8944
                        else check1 bvs2
                     in
                  let uu____8951 =
                    let uu____8953 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8953  in
                  if uu____8951
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8960 = check1 bvs  in
                     bind uu____8960
                       (fun uu____8966  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8968 =
                            let uu____8975 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8975  in
                          bind uu____8968
                            (fun uu____8985  ->
                               match uu____8985 with
                               | (ut,uvar_ut) ->
                                   let uu____8994 = set_solution goal ut  in
                                   bind uu____8994
                                     (fun uu____8999  ->
                                        let uu____9000 =
=======
                        let uu____8944 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8944
                        then
                          let uu____8949 =
                            let uu____8951 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8951
                             in
                          fail uu____8949
                        else check1 bvs2
                     in
                  let uu____8956 =
                    let uu____8958 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8958  in
                  if uu____8956
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8965 = check1 bvs  in
                     bind uu____8965
                       (fun uu____8971  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8973 =
                            let uu____8980 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8980  in
                          bind uu____8973
                            (fun uu____8990  ->
                               match uu____8990 with
                               | (ut,uvar_ut) ->
                                   let uu____8999 = set_solution goal ut  in
                                   bind uu____8999
                                     (fun uu____9004  ->
                                        let uu____9005 =
>>>>>>> snap
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
<<<<<<< HEAD
                                        replace_cur uu____9000))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____9008  ->
    let uu____9011 = cur_goal ()  in
    bind uu____9011
      (fun goal  ->
         let uu____9017 =
           let uu____9024 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9024  in
         match uu____9017 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9033) ->
             let uu____9038 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9038)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9051 = cur_goal ()  in
    bind uu____9051
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9061 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9061  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9064  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9077 = cur_goal ()  in
    bind uu____9077
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9087 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9087  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9090  -> add_goals [g']))
=======
                                        replace_cur uu____9005))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____9013  ->
    let uu____9016 = cur_goal ()  in
    bind uu____9016
      (fun goal  ->
         let uu____9022 =
           let uu____9029 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9029  in
         match uu____9022 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9038) ->
             let uu____9043 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9043)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9056 = cur_goal ()  in
    bind uu____9056
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9066 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9066  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9069  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9082 = cur_goal ()  in
    bind uu____9082
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9092 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9092  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9095  -> add_goals [g']))
>>>>>>> snap
  
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
<<<<<<< HEAD
            let uu____9131 = FStar_Syntax_Subst.compress t  in
            uu____9131.FStar_Syntax_Syntax.n  in
          let uu____9134 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1401_9141 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1401_9141.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1401_9141.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9134
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9158 =
                   let uu____9159 = FStar_Syntax_Subst.compress t1  in
                   uu____9159.FStar_Syntax_Syntax.n  in
                 match uu____9158 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9190 = ff hd1  in
                     bind uu____9190
                       (fun hd2  ->
                          let fa uu____9216 =
                            match uu____9216 with
                            | (a,q) ->
                                let uu____9237 = ff a  in
                                bind uu____9237 (fun a1  -> ret (a1, q))
                             in
                          let uu____9256 = mapM fa args  in
                          bind uu____9256
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9338 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9338 with
                      | (bs1,t') ->
                          let uu____9347 =
                            let uu____9350 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9350 t'  in
                          bind uu____9347
                            (fun t''  ->
                               let uu____9354 =
                                 let uu____9355 =
                                   let uu____9374 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9383 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9374, uu____9383, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9355  in
                               ret uu____9354))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9458 = ff hd1  in
                     bind uu____9458
                       (fun hd2  ->
                          let ffb br =
                            let uu____9473 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9473 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9505 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9505  in
                                let uu____9506 = ff1 e  in
                                bind uu____9506
=======
            let uu____9136 = FStar_Syntax_Subst.compress t  in
            uu____9136.FStar_Syntax_Syntax.n  in
          let uu____9139 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1402_9146 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1402_9146.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1402_9146.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9139
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9163 =
                   let uu____9164 = FStar_Syntax_Subst.compress t1  in
                   uu____9164.FStar_Syntax_Syntax.n  in
                 match uu____9163 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9195 = ff hd1  in
                     bind uu____9195
                       (fun hd2  ->
                          let fa uu____9221 =
                            match uu____9221 with
                            | (a,q) ->
                                let uu____9242 = ff a  in
                                bind uu____9242 (fun a1  -> ret (a1, q))
                             in
                          let uu____9261 = mapM fa args  in
                          bind uu____9261
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9343 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9343 with
                      | (bs1,t') ->
                          let uu____9352 =
                            let uu____9355 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9355 t'  in
                          bind uu____9352
                            (fun t''  ->
                               let uu____9359 =
                                 let uu____9360 =
                                   let uu____9379 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9388 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9379, uu____9388, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9360  in
                               ret uu____9359))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9463 = ff hd1  in
                     bind uu____9463
                       (fun hd2  ->
                          let ffb br =
                            let uu____9478 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9478 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9510 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9510  in
                                let uu____9511 = ff1 e  in
                                bind uu____9511
>>>>>>> snap
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
<<<<<<< HEAD
                          let uu____9521 = mapM ffb brs  in
                          bind uu____9521
=======
                          let uu____9526 = mapM ffb brs  in
                          bind uu____9526
>>>>>>> snap
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
<<<<<<< HEAD
                          FStar_Syntax_Syntax.lbunivs = uu____9565;
                          FStar_Syntax_Syntax.lbtyp = uu____9566;
                          FStar_Syntax_Syntax.lbeff = uu____9567;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9569;
                          FStar_Syntax_Syntax.lbpos = uu____9570;_}::[]),e)
                     ->
                     let lb =
                       let uu____9598 =
                         let uu____9599 = FStar_Syntax_Subst.compress t1  in
                         uu____9599.FStar_Syntax_Syntax.n  in
                       match uu____9598 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9603) -> lb
                       | uu____9619 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9629 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9629
                         (fun def1  ->
                            ret
                              (let uu___1354_9635 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1354_9635.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1354_9635.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1354_9635.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1354_9635.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1354_9635.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1354_9635.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9636 = fflb lb  in
                     bind uu____9636
                       (fun lb1  ->
                          let uu____9646 =
                            let uu____9651 =
                              let uu____9652 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9652]  in
                            FStar_Syntax_Subst.open_term uu____9651 e  in
                          match uu____9646 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9682 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9682  in
                              let uu____9683 = ff1 e1  in
                              bind uu____9683
=======
                          FStar_Syntax_Syntax.lbunivs = uu____9570;
                          FStar_Syntax_Syntax.lbtyp = uu____9571;
                          FStar_Syntax_Syntax.lbeff = uu____9572;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9574;
                          FStar_Syntax_Syntax.lbpos = uu____9575;_}::[]),e)
                     ->
                     let lb =
                       let uu____9603 =
                         let uu____9604 = FStar_Syntax_Subst.compress t1  in
                         uu____9604.FStar_Syntax_Syntax.n  in
                       match uu____9603 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9608) -> lb
                       | uu____9624 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9634 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9634
                         (fun def1  ->
                            ret
                              (let uu___1355_9640 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1355_9640.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1355_9640.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1355_9640.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1355_9640.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1355_9640.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1355_9640.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9641 = fflb lb  in
                     bind uu____9641
                       (fun lb1  ->
                          let uu____9651 =
                            let uu____9656 =
                              let uu____9657 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9657]  in
                            FStar_Syntax_Subst.open_term uu____9656 e  in
                          match uu____9651 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9687 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9687  in
                              let uu____9688 = ff1 e1  in
                              bind uu____9688
>>>>>>> snap
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
<<<<<<< HEAD
                       let uu____9730 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9730
                         (fun def  ->
                            ret
                              (let uu___1372_9736 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1372_9736.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1372_9736.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1372_9736.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1372_9736.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1372_9736.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1372_9736.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9737 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9737 with
                      | (lbs1,e1) ->
                          let uu____9752 = mapM fflb lbs1  in
                          bind uu____9752
                            (fun lbs2  ->
                               let uu____9764 = ff e1  in
                               bind uu____9764
                                 (fun e2  ->
                                    let uu____9772 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9772 with
=======
                       let uu____9735 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9735
                         (fun def  ->
                            ret
                              (let uu___1373_9741 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1373_9741.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1373_9741.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1373_9741.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1373_9741.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1373_9741.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1373_9741.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9742 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9742 with
                      | (lbs1,e1) ->
                          let uu____9757 = mapM fflb lbs1  in
                          bind uu____9757
                            (fun lbs2  ->
                               let uu____9769 = ff e1  in
                               bind uu____9769
                                 (fun e2  ->
                                    let uu____9777 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9777 with
>>>>>>> snap
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
<<<<<<< HEAD
                     let uu____9843 = ff t2  in
                     bind uu____9843
=======
                     let uu____9848 = ff t2  in
                     bind uu____9848
>>>>>>> snap
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
<<<<<<< HEAD
                     let uu____9874 = ff t2  in
                     bind uu____9874
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9881 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1396_9888 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1396_9888.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1396_9888.FStar_Syntax_Syntax.vars)
=======
                     let uu____9879 = ff t2  in
                     bind uu____9879
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9886 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1397_9893 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1397_9893.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1397_9893.FStar_Syntax_Syntax.vars)
>>>>>>> snap
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
<<<<<<< HEAD
              let uu____9935 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1409_9944 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1409_9944.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1409_9944.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1409_9944.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1409_9944.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1409_9944.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1409_9944.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1409_9944.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1409_9944.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1409_9944.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
<<<<<<< HEAD
                       (uu___1409_9944.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1409_9944.FStar_TypeChecker_Env.is_pattern);
=======
                       (uu___1409_9935.FStar_TypeChecker_Env.attrtab);
>>>>>>> snap
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1409_9944.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1409_9944.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1409_9944.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1409_9944.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1409_9944.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1409_9944.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1409_9944.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1409_9944.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1409_9944.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1409_9944.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1409_9944.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1409_9944.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1409_9944.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1409_9944.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1409_9944.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1409_9944.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1409_9944.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1409_9944.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1409_9944.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1409_9944.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1409_9944.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1409_9944.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1409_9944.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1409_9944.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1409_9944.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1409_9944.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1409_9944.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1409_9944.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1409_9944.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1409_9944.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1409_9944.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
                       (uu___1409_9944.FStar_TypeChecker_Env.strict_args_tab)
=======
                       (uu___1409_9935.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___1409_9935.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
                   }) t
                 in
              match uu____9935 with
              | (t1,lcomp,g) ->
                  let uu____9951 =
                    (let uu____9955 =
                       FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp
                        in
                     Prims.op_Negation uu____9955) ||
                      (let uu____9958 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9958)
                     in
                  if uu____9951
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_TypeChecker_Common.res_typ  in
                       let uu____9969 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9969
                         (fun uu____9986  ->
                            match uu____9986 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9999  ->
                                      let uu____10000 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____10002 =
=======
              let uu____9940 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1410_9949 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1410_9949.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1410_9949.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1410_9949.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1410_9949.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1410_9949.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1410_9949.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1410_9949.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1410_9949.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1410_9949.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1410_9949.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1410_9949.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1410_9949.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1410_9949.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1410_9949.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1410_9949.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1410_9949.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1410_9949.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1410_9949.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1410_9949.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1410_9949.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1410_9949.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1410_9949.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1410_9949.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1410_9949.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1410_9949.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1410_9949.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1410_9949.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1410_9949.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1410_9949.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1410_9949.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1410_9949.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1410_9949.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1410_9949.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1410_9949.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1410_9949.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___1410_9949.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1410_9949.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1410_9949.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1410_9949.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1410_9949.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1410_9949.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1410_9949.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___1410_9949.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___1410_9949.FStar_TypeChecker_Env.erasable_types_tab)
                   }) t
                 in
              match uu____9940 with
              | (t1,lcomp,g) ->
                  let uu____9956 =
                    (let uu____9960 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9960) ||
                      (let uu____9963 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9963)
                     in
                  if uu____9956
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9974 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9974
                         (fun uu____9991  ->
                            match uu____9991 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____10004  ->
                                      let uu____10005 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____10007 =
>>>>>>> snap
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
<<<<<<< HEAD
                                        uu____10000 uu____10002);
                                 (let uu____10005 =
                                    let uu____10008 =
                                      let uu____10009 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10009
=======
                                        uu____10005 uu____10007);
                                 (let uu____10010 =
                                    let uu____10013 =
                                      let uu____10014 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10014
>>>>>>> snap
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
<<<<<<< HEAD
                                      uu____10008 opts label1
                                     in
                                  bind uu____10005
                                    (fun uu____10013  ->
                                       let uu____10014 =
                                         bind tau
                                           (fun uu____10020  ->
=======
                                      uu____10013 opts label1
                                     in
                                  bind uu____10010
                                    (fun uu____10018  ->
                                       let uu____10019 =
                                         bind tau
                                           (fun uu____10025  ->
>>>>>>> snap
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
<<<<<<< HEAD
                                                (fun uu____10026  ->
                                                   let uu____10027 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____10029 =
=======
                                                (fun uu____10031  ->
                                                   let uu____10032 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____10034 =
>>>>>>> snap
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
<<<<<<< HEAD
                                                     uu____10027 uu____10029);
                                              ret ut1)
                                          in
                                       focus uu____10014))))
                        in
                     let uu____10032 = catch rewrite_eq  in
                     bind uu____10032
=======
                                                     uu____10032 uu____10034);
                                              ret ut1)
                                          in
                                       focus uu____10019))))
                        in
                     let uu____10037 = catch rewrite_eq  in
                     bind uu____10037
>>>>>>> snap
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
<<<<<<< HEAD
          let uu____10244 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10244
            (fun t1  ->
               let uu____10252 =
                 f env
                   (let uu___1486_10260 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1486_10260.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1486_10260.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10252
                 (fun uu____10276  ->
                    match uu____10276 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10299 =
                               let uu____10300 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10300.FStar_Syntax_Syntax.n  in
                             match uu____10299 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10337 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10337
                                   (fun uu____10359  ->
                                      match uu____10359 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10375 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10375
                                            (fun uu____10399  ->
                                               match uu____10399 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1466_10429 =
=======
          let uu____10249 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10249
            (fun t1  ->
               let uu____10257 =
                 f env
                   (let uu___1487_10265 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1487_10265.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1487_10265.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10257
                 (fun uu____10281  ->
                    match uu____10281 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10304 =
                               let uu____10305 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10305.FStar_Syntax_Syntax.n  in
                             match uu____10304 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10342 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10342
                                   (fun uu____10364  ->
                                      match uu____10364 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10380 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10380
                                            (fun uu____10404  ->
                                               match uu____10404 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1467_10434 =
>>>>>>> snap
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
<<<<<<< HEAD
                                                           (uu___1466_10429.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1466_10429.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10471 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10471 with
                                  | (bs1,t') ->
                                      let uu____10486 =
                                        let uu____10493 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10493 ctrl1 t'
                                         in
                                      bind uu____10486
                                        (fun uu____10508  ->
                                           match uu____10508 with
                                           | (t'',ctrl2) ->
                                               let uu____10523 =
                                                 let uu____10530 =
                                                   let uu___1479_10533 = t4
                                                      in
                                                   let uu____10536 =
                                                     let uu____10537 =
                                                       let uu____10556 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10565 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10556,
                                                         uu____10565, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10537
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10536;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1479_10533.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1479_10533.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10530, ctrl2)  in
                                               ret uu____10523))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10618 -> ret (t3, ctrl1))))
=======
                                                           (uu___1467_10434.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1467_10434.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10476 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10476 with
                                  | (bs1,t') ->
                                      let uu____10491 =
                                        let uu____10498 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10498 ctrl1 t'
                                         in
                                      bind uu____10491
                                        (fun uu____10513  ->
                                           match uu____10513 with
                                           | (t'',ctrl2) ->
                                               let uu____10528 =
                                                 let uu____10535 =
                                                   let uu___1480_10538 = t4
                                                      in
                                                   let uu____10541 =
                                                     let uu____10542 =
                                                       let uu____10561 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10570 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10561,
                                                         uu____10570, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10542
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10541;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1480_10538.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1480_10538.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10535, ctrl2)  in
                                               ret uu____10528))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10623 -> ret (t3, ctrl1))))
>>>>>>> snap

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
<<<<<<< HEAD
              let uu____10664 = ctrl_tac_fold f env ctrl t  in
              bind uu____10664
                (fun uu____10685  ->
                   match uu____10685 with
                   | (t1,ctrl1) ->
                       let uu____10700 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10700
                         (fun uu____10724  ->
                            match uu____10724 with
=======
              let uu____10669 = ctrl_tac_fold f env ctrl t  in
              bind uu____10669
                (fun uu____10690  ->
                   match uu____10690 with
                   | (t1,ctrl1) ->
                       let uu____10705 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10705
                         (fun uu____10729  ->
                            match uu____10729 with
>>>>>>> snap
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
<<<<<<< HEAD
                let uu____10815 =
                  let uu____10823 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10823
                    (fun uu____10834  ->
                       let uu____10835 = ctrl t1  in
                       bind uu____10835
                         (fun res  ->
                            let uu____10861 = trivial ()  in
                            bind uu____10861 (fun uu____10870  -> ret res)))
                   in
                bind uu____10815
                  (fun uu____10888  ->
                     match uu____10888 with
=======
                let uu____10820 =
                  let uu____10828 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10828
                    (fun uu____10839  ->
                       let uu____10840 = ctrl t1  in
                       bind uu____10840
                         (fun res  ->
                            let uu____10866 = trivial ()  in
                            bind uu____10866 (fun uu____10875  -> ret res)))
                   in
                bind uu____10820
                  (fun uu____10893  ->
                     match uu____10893 with
>>>>>>> snap
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
<<<<<<< HEAD
                           (let uu____10917 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1516_10926 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1516_10926.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1516_10926.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1516_10926.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1516_10926.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1516_10926.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1516_10926.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1516_10926.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1516_10926.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1516_10926.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
<<<<<<< HEAD
                                     (uu___1516_10926.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1516_10926.FStar_TypeChecker_Env.is_pattern);
=======
                                     (uu___1516_10917.FStar_TypeChecker_Env.attrtab);
>>>>>>> snap
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1516_10926.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1516_10926.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1516_10926.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1516_10926.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1516_10926.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1516_10926.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1516_10926.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1516_10926.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1516_10926.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1516_10926.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1516_10926.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1516_10926.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1516_10926.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1516_10926.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1516_10926.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1516_10926.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1516_10926.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1516_10926.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1516_10926.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1516_10926.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1516_10926.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1516_10926.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1516_10926.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1516_10926.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1516_10926.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1516_10926.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1516_10926.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1516_10926.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1516_10926.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1516_10926.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1516_10926.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
                                     (uu___1516_10926.FStar_TypeChecker_Env.strict_args_tab)
=======
                                     (uu___1516_10917.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___1516_10917.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
                                 }) t1
                               in
                            match uu____10917 with
                            | (t2,lcomp,g) ->
                                let uu____10937 =
                                  (let uu____10941 =
                                     FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10941) ||
                                    (let uu____10944 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10944)
                                   in
                                if uu____10937
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_TypeChecker_Common.res_typ
                                      in
                                   let uu____10960 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10960
                                     (fun uu____10981  ->
                                        match uu____10981 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10998  ->
                                                  let uu____10999 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____11001 =
=======
                           (let uu____10922 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1517_10931 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1517_10931.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1517_10931.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1517_10931.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1517_10931.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1517_10931.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1517_10931.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1517_10931.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1517_10931.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1517_10931.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1517_10931.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1517_10931.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1517_10931.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1517_10931.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1517_10931.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1517_10931.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1517_10931.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1517_10931.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1517_10931.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1517_10931.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1517_10931.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1517_10931.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1517_10931.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1517_10931.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1517_10931.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1517_10931.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1517_10931.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1517_10931.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1517_10931.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1517_10931.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1517_10931.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1517_10931.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1517_10931.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1517_10931.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1517_10931.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1517_10931.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___1517_10931.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1517_10931.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1517_10931.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1517_10931.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1517_10931.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1517_10931.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1517_10931.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___1517_10931.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___1517_10931.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t1
                               in
                            match uu____10922 with
                            | (t2,lcomp,g) ->
                                let uu____10942 =
                                  (let uu____10946 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10946) ||
                                    (let uu____10949 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10949)
                                   in
                                if uu____10942
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10965 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10965
                                     (fun uu____10986  ->
                                        match uu____10986 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____11003  ->
                                                  let uu____11004 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____11006 =
>>>>>>> snap
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
<<<<<<< HEAD
                                                    uu____10999 uu____11001);
                                             (let uu____11004 =
                                                let uu____11007 =
                                                  let uu____11008 =
=======
                                                    uu____11004 uu____11006);
                                             (let uu____11009 =
                                                let uu____11012 =
                                                  let uu____11013 =
>>>>>>> snap
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
<<<<<<< HEAD
                                                    uu____11008 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____11007 opts label1
                                                 in
                                              bind uu____11004
                                                (fun uu____11016  ->
                                                   let uu____11017 =
                                                     bind rewriter
                                                       (fun uu____11031  ->
=======
                                                    uu____11013 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____11012 opts label1
                                                 in
                                              bind uu____11009
                                                (fun uu____11021  ->
                                                   let uu____11022 =
                                                     bind rewriter
                                                       (fun uu____11036  ->
>>>>>>> snap
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
<<<<<<< HEAD
                                                            (fun uu____11037 
                                                               ->
                                                               let uu____11038
=======
                                                            (fun uu____11042 
                                                               ->
                                                               let uu____11043
>>>>>>> snap
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
<<<<<<< HEAD
                                                               let uu____11040
=======
                                                               let uu____11045
>>>>>>> snap
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
<<<<<<< HEAD
                                                                 uu____11038
                                                                 uu____11040);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11017)))))))
=======
                                                                 uu____11043
                                                                 uu____11045);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11022)))))))
>>>>>>> snap
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
<<<<<<< HEAD
      let uu____11085 =
        bind get
          (fun ps  ->
             let uu____11095 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11095 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11133  ->
                       let uu____11134 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11134);
                  bind dismiss_all
                    (fun uu____11139  ->
                       let uu____11140 =
                         let uu____11147 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11147
                           keepGoing gt1
                          in
                       bind uu____11140
                         (fun uu____11157  ->
                            match uu____11157 with
                            | (gt',uu____11165) ->
                                (log ps
                                   (fun uu____11169  ->
                                      let uu____11170 =
=======
      let uu____11090 =
        bind get
          (fun ps  ->
             let uu____11100 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11100 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11138  ->
                       let uu____11139 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11139);
                  bind dismiss_all
                    (fun uu____11144  ->
                       let uu____11145 =
                         let uu____11152 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11152
                           keepGoing gt1
                          in
                       bind uu____11145
                         (fun uu____11162  ->
                            match uu____11162 with
                            | (gt',uu____11170) ->
                                (log ps
                                   (fun uu____11174  ->
                                      let uu____11175 =
>>>>>>> snap
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
<<<<<<< HEAD
                                        uu____11170);
                                 (let uu____11173 = push_goals gs  in
                                  bind uu____11173
                                    (fun uu____11178  ->
                                       let uu____11179 =
                                         let uu____11182 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____11182]  in
                                       add_goals uu____11179)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11085
=======
                                        uu____11175);
                                 (let uu____11178 = push_goals gs  in
                                  bind uu____11178
                                    (fun uu____11183  ->
                                       let uu____11184 =
                                         let uu____11187 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____11187]  in
                                       add_goals uu____11184)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11090
>>>>>>> snap
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
<<<<<<< HEAD
      let uu____11207 =
        bind get
          (fun ps  ->
             let uu____11217 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11217 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11255  ->
                       let uu____11256 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11256);
                  bind dismiss_all
                    (fun uu____11261  ->
                       let uu____11262 =
                         let uu____11265 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11265 gt1
                          in
                       bind uu____11262
                         (fun gt'  ->
                            log ps
                              (fun uu____11273  ->
                                 let uu____11274 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11274);
                            (let uu____11277 = push_goals gs  in
                             bind uu____11277
                               (fun uu____11282  ->
                                  let uu____11283 =
                                    let uu____11286 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11286]  in
                                  add_goals uu____11283))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____11207
=======
      let uu____11212 =
        bind get
          (fun ps  ->
             let uu____11222 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11222 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11260  ->
                       let uu____11261 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11261);
                  bind dismiss_all
                    (fun uu____11266  ->
                       let uu____11267 =
                         let uu____11270 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11270 gt1
                          in
                       bind uu____11267
                         (fun gt'  ->
                            log ps
                              (fun uu____11278  ->
                                 let uu____11279 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11279);
                            (let uu____11282 = push_goals gs  in
                             bind uu____11282
                               (fun uu____11287  ->
                                  let uu____11288 =
                                    let uu____11291 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11291]  in
                                  add_goals uu____11288))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____11212
>>>>>>> snap
  
let (_trefl :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit tac) =
  fun l  ->
    fun r  ->
<<<<<<< HEAD
      let uu____11307 = cur_goal ()  in
      bind uu____11307
        (fun g  ->
           let uu____11313 =
             let uu____11317 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11317 l r  in
           bind uu____11313
=======
      let uu____11312 = cur_goal ()  in
      bind uu____11312
        (fun g  ->
           let uu____11318 =
             let uu____11322 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11322 l r  in
           bind uu____11318
>>>>>>> snap
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
<<<<<<< HEAD
                     let uu____11328 = FStar_Tactics_Types.goal_env g  in
=======
                     let uu____11333 = FStar_Tactics_Types.goal_env g  in
>>>>>>> snap
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
<<<<<<< HEAD
                       FStar_TypeChecker_Env.UnfoldTac] uu____11328 l
                      in
                   let r1 =
                     let uu____11330 = FStar_Tactics_Types.goal_env g  in
=======
                       FStar_TypeChecker_Env.UnfoldTac] uu____11333 l
                      in
                   let r1 =
                     let uu____11335 = FStar_Tactics_Types.goal_env g  in
>>>>>>> snap
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
<<<<<<< HEAD
                       FStar_TypeChecker_Env.UnfoldTac] uu____11330 r
                      in
                   let uu____11331 =
                     let uu____11335 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11335 l1 r1  in
                   bind uu____11331
=======
                       FStar_TypeChecker_Env.UnfoldTac] uu____11335 r
                      in
                   let uu____11336 =
                     let uu____11340 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11340 l1 r1  in
                   bind uu____11336
>>>>>>> snap
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
<<<<<<< HEAD
                          (let uu____11345 =
                             let uu____11347 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11347 l1  in
                           let uu____11348 =
                             let uu____11350 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11350 r1  in
                           fail2 "not a trivial equality ((%s) vs (%s))"
                             uu____11345 uu____11348)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11359  ->
    let uu____11362 =
      let uu____11365 = cur_goal ()  in
      bind uu____11365
        (fun g  ->
           let uu____11373 =
             let uu____11380 = FStar_Tactics_Types.goal_type g  in
             destruct_eq uu____11380  in
           match uu____11373 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11393 =
                 let uu____11395 = FStar_Tactics_Types.goal_env g  in
                 let uu____11396 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11395 uu____11396  in
               fail1 "not an equality (%s)" uu____11393)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11362
  
let (dup : unit -> unit tac) =
  fun uu____11410  ->
    let uu____11413 = cur_goal ()  in
    bind uu____11413
      (fun g  ->
         let uu____11419 =
           let uu____11426 = FStar_Tactics_Types.goal_env g  in
           let uu____11427 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11426 uu____11427  in
         bind uu____11419
           (fun uu____11437  ->
              match uu____11437 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1596_11447 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1596_11447.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1596_11447.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1596_11447.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1596_11447.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11450  ->
                       let uu____11451 =
                         let uu____11454 = FStar_Tactics_Types.goal_env g  in
                         let uu____11455 =
                           let uu____11456 =
                             let uu____11457 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11458 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11457
                               uu____11458
                              in
                           let uu____11459 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11460 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11456 uu____11459 u
                             uu____11460
                            in
                         add_irrelevant_goal "dup equation" uu____11454
                           uu____11455 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11451
                         (fun uu____11464  ->
                            let uu____11465 = add_goals [g']  in
                            bind uu____11465 (fun uu____11469  -> ret ())))))
=======
                          (let uu____11350 =
                             let uu____11352 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11352 l1  in
                           let uu____11353 =
                             let uu____11355 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11355 r1  in
                           fail2 "not a trivial equality ((%s) vs (%s))"
                             uu____11350 uu____11353)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11364  ->
    let uu____11367 =
      let uu____11370 = cur_goal ()  in
      bind uu____11370
        (fun g  ->
           let uu____11378 =
             let uu____11385 = FStar_Tactics_Types.goal_type g  in
             destruct_eq uu____11385  in
           match uu____11378 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11398 =
                 let uu____11400 = FStar_Tactics_Types.goal_env g  in
                 let uu____11401 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11400 uu____11401  in
               fail1 "not an equality (%s)" uu____11398)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11367
  
let (dup : unit -> unit tac) =
  fun uu____11415  ->
    let uu____11418 = cur_goal ()  in
    bind uu____11418
      (fun g  ->
         let uu____11424 =
           let uu____11431 = FStar_Tactics_Types.goal_env g  in
           let uu____11432 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11431 uu____11432  in
         bind uu____11424
           (fun uu____11442  ->
              match uu____11442 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1597_11452 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1597_11452.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1597_11452.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1597_11452.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1597_11452.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11455  ->
                       let uu____11456 =
                         let uu____11459 = FStar_Tactics_Types.goal_env g  in
                         let uu____11460 =
                           let uu____11461 =
                             let uu____11462 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11463 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11462
                               uu____11463
                              in
                           let uu____11464 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11465 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11461 uu____11464 u
                             uu____11465
                            in
                         add_irrelevant_goal "dup equation" uu____11459
                           uu____11460 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11456
                         (fun uu____11469  ->
                            let uu____11470 = add_goals [g']  in
                            bind uu____11470 (fun uu____11474  -> ret ())))))
>>>>>>> snap
  
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
<<<<<<< HEAD
              let uu____11595 = f x y  in
              if uu____11595 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11618 -> (acc, l11, l21)  in
        let uu____11633 = aux [] l1 l2  in
        match uu____11633 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
=======
              let uu____11600 = f x y  in
              if uu____11600 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11623 -> (acc, l11, l21)  in
        let uu____11638 = aux [] l1 l2  in
        match uu____11638 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
>>>>>>> snap
  
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
<<<<<<< HEAD
      let uu____11739 = get_phi g1  in
      match uu____11739 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11746 = get_phi g2  in
          (match uu____11746 with
=======
      let uu____11744 = get_phi g1  in
      match uu____11744 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11751 = get_phi g2  in
          (match uu____11751 with
>>>>>>> snap
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
<<<<<<< HEAD
               let uu____11759 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11759 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11790 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11790 phi1  in
                    let t2 =
                      let uu____11800 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11800 phi2  in
                    let uu____11809 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11809
                      (fun uu____11814  ->
                         let uu____11815 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11815
                           (fun uu____11822  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1647_11827 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11828 =
=======
               let uu____11764 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11764 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11795 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11795 phi1  in
                    let t2 =
                      let uu____11805 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11805 phi2  in
                    let uu____11814 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11814
                      (fun uu____11819  ->
                         let uu____11820 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11820
                           (fun uu____11827  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1648_11832 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11833 =
>>>>>>> snap
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
<<<<<<< HEAD
                                    (uu___1647_11827.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1647_11827.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1647_11827.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1647_11827.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11828;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1647_11827.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1647_11827.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1647_11827.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
<<<<<<< HEAD
                                    (uu___1647_11827.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1647_11827.FStar_TypeChecker_Env.is_pattern);
=======
                                    (uu___1647_11818.FStar_TypeChecker_Env.attrtab);
>>>>>>> snap
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1647_11827.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1647_11827.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1647_11827.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1647_11827.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1647_11827.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1647_11827.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1647_11827.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1647_11827.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1647_11827.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1647_11827.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1647_11827.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1647_11827.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1647_11827.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1647_11827.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1647_11827.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1647_11827.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1647_11827.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1647_11827.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1647_11827.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1647_11827.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1647_11827.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1647_11827.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1647_11827.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1647_11827.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1647_11827.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1647_11827.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1647_11827.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1647_11827.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1647_11827.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1647_11827.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1647_11827.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1647_11827.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
                                    (uu___1647_11827.FStar_TypeChecker_Env.strict_args_tab)
=======
                                    (uu___1647_11818.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1647_11818.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
                                }  in
                              let uu____11832 =
=======
                                    (uu___1648_11832.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1648_11832.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1648_11832.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1648_11832.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11833;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1648_11832.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1648_11832.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1648_11832.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1648_11832.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1648_11832.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1648_11832.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1648_11832.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1648_11832.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1648_11832.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1648_11832.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1648_11832.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1648_11832.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1648_11832.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1648_11832.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1648_11832.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1648_11832.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1648_11832.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1648_11832.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1648_11832.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1648_11832.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1648_11832.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1648_11832.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1648_11832.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1648_11832.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1648_11832.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1648_11832.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1648_11832.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1648_11832.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1648_11832.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1648_11832.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1648_11832.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1648_11832.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1648_11832.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1648_11832.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1648_11832.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1648_11832.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1648_11832.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1648_11832.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1648_11832.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let uu____11837 =
>>>>>>> snap
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
<<<<<<< HEAD
                              bind uu____11832
                                (fun goal  ->
                                   mlog
                                     (fun uu____11842  ->
                                        let uu____11843 =
                                          goal_to_string_verbose g1  in
                                        let uu____11845 =
                                          goal_to_string_verbose g2  in
                                        let uu____11847 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11843 uu____11845 uu____11847)
                                     (fun uu____11851  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11859  ->
=======
                              bind uu____11837
                                (fun goal  ->
                                   mlog
                                     (fun uu____11847  ->
                                        let uu____11848 =
                                          goal_to_string_verbose g1  in
                                        let uu____11850 =
                                          goal_to_string_verbose g2  in
                                        let uu____11852 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11848 uu____11850 uu____11852)
                                     (fun uu____11856  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11864  ->
>>>>>>> snap
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
<<<<<<< HEAD
             let uu____11875 =
               set
                 (let uu___1662_11880 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1662_11880.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1662_11880.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1662_11880.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1662_11880.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1662_11880.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1662_11880.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1662_11880.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1662_11880.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1662_11880.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1662_11880.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1662_11880.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1662_11880.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11875
               (fun uu____11883  ->
                  let uu____11884 = join_goals g1 g2  in
                  bind uu____11884 (fun g12  -> add_goals [g12]))
         | uu____11889 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11905 =
      let uu____11908 = cur_goal ()  in
      bind uu____11908
        (fun g  ->
           FStar_Options.push ();
           (let uu____11921 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11921);
=======
             let uu____11880 =
               set
                 (let uu___1663_11885 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1663_11885.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1663_11885.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1663_11885.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1663_11885.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1663_11885.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1663_11885.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1663_11885.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1663_11885.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1663_11885.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1663_11885.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1663_11885.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11880
               (fun uu____11888  ->
                  let uu____11889 = join_goals g1 g2  in
                  bind uu____11889 (fun g12  -> add_goals [g12]))
         | uu____11894 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11910 =
      let uu____11913 = cur_goal ()  in
      bind uu____11913
        (fun g  ->
           FStar_Options.push ();
           (let uu____11926 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11926);
>>>>>>> snap
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
<<<<<<< HEAD
                   let uu___1673_11928 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1673_11928.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1673_11928.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1673_11928.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1673_11928.FStar_Tactics_Types.label)
=======
                   let uu___1674_11933 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1674_11933.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1674_11933.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1674_11933.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1674_11933.FStar_Tactics_Types.label)
>>>>>>> snap
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
<<<<<<< HEAD
    FStar_All.pipe_left (wrap_err "set_options") uu____11905
  
let (top_env : unit -> env tac) =
  fun uu____11945  ->
=======
    FStar_All.pipe_left (wrap_err "set_options") uu____11910
  
let (top_env : unit -> env tac) =
  fun uu____11950  ->
>>>>>>> snap
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
<<<<<<< HEAD
  fun uu____11960  ->
    let uu____11964 = cur_goal ()  in
    bind uu____11964
      (fun g  ->
         let uu____11971 =
           (FStar_Options.lax ()) ||
             (let uu____11974 = FStar_Tactics_Types.goal_env g  in
              uu____11974.FStar_TypeChecker_Env.lax)
            in
         ret uu____11971)
=======
  fun uu____11965  ->
    let uu____11969 = cur_goal ()  in
    bind uu____11969
      (fun g  ->
         let uu____11976 =
           (FStar_Options.lax ()) ||
             (let uu____11979 = FStar_Tactics_Types.goal_env g  in
              uu____11979.FStar_TypeChecker_Env.lax)
            in
         ret uu____11976)
>>>>>>> snap
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
<<<<<<< HEAD
      let uu____11991 =
        mlog
          (fun uu____11996  ->
             let uu____11997 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11997)
          (fun uu____12002  ->
             let uu____12003 = cur_goal ()  in
             bind uu____12003
               (fun goal  ->
                  let env =
                    let uu____12011 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12011 ty  in
                  let uu____12012 = __tc_ghost env tm  in
                  bind uu____12012
                    (fun uu____12031  ->
                       match uu____12031 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12045  ->
                                let uu____12046 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12046)
                             (fun uu____12050  ->
                                mlog
                                  (fun uu____12053  ->
                                     let uu____12054 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12054)
                                  (fun uu____12059  ->
                                     let uu____12060 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12060
                                       (fun uu____12065  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11991
=======
      let uu____11996 =
        mlog
          (fun uu____12001  ->
             let uu____12002 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____12002)
          (fun uu____12007  ->
             let uu____12008 = cur_goal ()  in
             bind uu____12008
               (fun goal  ->
                  let env =
                    let uu____12016 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12016 ty  in
                  let uu____12017 = __tc_ghost env tm  in
                  bind uu____12017
                    (fun uu____12036  ->
                       match uu____12036 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12050  ->
                                let uu____12051 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12051)
                             (fun uu____12055  ->
                                mlog
                                  (fun uu____12058  ->
                                     let uu____12059 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12059)
                                  (fun uu____12064  ->
                                     let uu____12065 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12065
                                       (fun uu____12070  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11996
>>>>>>> snap
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
<<<<<<< HEAD
      let uu____12090 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12096 =
              let uu____12103 =
                let uu____12104 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12104
                 in
              new_uvar "uvar_env.2" env uu____12103  in
            bind uu____12096
              (fun uu____12121  ->
                 match uu____12121 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12090
        (fun typ  ->
           let uu____12133 = new_uvar "uvar_env" env typ  in
           bind uu____12133
             (fun uu____12148  ->
                match uu____12148 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12167 =
=======
      let uu____12095 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12101 =
              let uu____12108 =
                let uu____12109 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12109
                 in
              new_uvar "uvar_env.2" env uu____12108  in
            bind uu____12101
              (fun uu____12126  ->
                 match uu____12126 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12095
        (fun typ  ->
           let uu____12138 = new_uvar "uvar_env" env typ  in
           bind uu____12138
             (fun uu____12153  ->
                match uu____12153 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12172 =
>>>>>>> snap
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
<<<<<<< HEAD
             | g::uu____12186 -> g.FStar_Tactics_Types.opts
             | uu____12189 -> FStar_Options.peek ()  in
           let uu____12192 = FStar_Syntax_Util.head_and_args t  in
           match uu____12192 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12212);
                FStar_Syntax_Syntax.pos = uu____12213;
                FStar_Syntax_Syntax.vars = uu____12214;_},uu____12215)
               ->
               let env1 =
                 let uu___1727_12257 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1727_12257.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1727_12257.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1727_12257.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1727_12257.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1727_12257.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1727_12257.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1727_12257.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1727_12257.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
<<<<<<< HEAD
                     (uu___1727_12257.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1727_12257.FStar_TypeChecker_Env.is_pattern);
=======
                     (uu___1727_12248.FStar_TypeChecker_Env.attrtab);
>>>>>>> snap
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1727_12257.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1727_12257.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1727_12257.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1727_12257.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1727_12257.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1727_12257.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1727_12257.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1727_12257.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1727_12257.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1727_12257.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1727_12257.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1727_12257.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1727_12257.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1727_12257.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1727_12257.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1727_12257.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1727_12257.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1727_12257.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1727_12257.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1727_12257.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1727_12257.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1727_12257.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1727_12257.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1727_12257.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1727_12257.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1727_12257.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1727_12257.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1727_12257.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1727_12257.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1727_12257.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1727_12257.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1727_12257.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
                     (uu___1727_12257.FStar_TypeChecker_Env.strict_args_tab)
=======
                     (uu___1727_12248.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1727_12248.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12261 =
                 let uu____12264 = bnorm_goal g  in [uu____12264]  in
               add_goals uu____12261
           | uu____12265 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12167
=======
             | g::uu____12191 -> g.FStar_Tactics_Types.opts
             | uu____12194 -> FStar_Options.peek ()  in
           let uu____12197 = FStar_Syntax_Util.head_and_args t  in
           match uu____12197 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12217);
                FStar_Syntax_Syntax.pos = uu____12218;
                FStar_Syntax_Syntax.vars = uu____12219;_},uu____12220)
               ->
               let env1 =
                 let uu___1728_12262 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1728_12262.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1728_12262.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1728_12262.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1728_12262.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1728_12262.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1728_12262.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1728_12262.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1728_12262.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1728_12262.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1728_12262.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1728_12262.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1728_12262.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1728_12262.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1728_12262.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1728_12262.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1728_12262.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1728_12262.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1728_12262.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1728_12262.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1728_12262.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1728_12262.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1728_12262.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1728_12262.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1728_12262.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1728_12262.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1728_12262.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1728_12262.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1728_12262.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1728_12262.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1728_12262.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1728_12262.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1728_12262.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1728_12262.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1728_12262.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1728_12262.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1728_12262.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1728_12262.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1728_12262.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1728_12262.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1728_12262.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1728_12262.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1728_12262.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1728_12262.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1728_12262.FStar_TypeChecker_Env.erasable_types_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12266 =
                 let uu____12269 = bnorm_goal g  in [uu____12269]  in
               add_goals uu____12266
           | uu____12270 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12172
>>>>>>> snap
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
<<<<<<< HEAD
             let uu____12327 = if b then t2 else ret false  in
             bind uu____12327 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12353 = trytac comp  in
      bind uu____12353
        (fun uu___4_12365  ->
           match uu___4_12365 with
=======
             let uu____12332 = if b then t2 else ret false  in
             bind uu____12332 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12358 = trytac comp  in
      bind uu____12358
        (fun uu___4_12370  ->
           match uu___4_12370 with
>>>>>>> snap
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
<<<<<<< HEAD
        let uu____12407 =
          bind get
            (fun ps  ->
               let uu____12415 = __tc e t1  in
               bind uu____12415
                 (fun uu____12436  ->
                    match uu____12436 with
                    | (t11,ty1,g1) ->
                        let uu____12449 = __tc e t2  in
                        bind uu____12449
                          (fun uu____12470  ->
                             match uu____12470 with
                             | (t21,ty2,g2) ->
                                 let uu____12483 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12483
                                   (fun uu____12490  ->
                                      let uu____12491 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12491
                                        (fun uu____12499  ->
                                           let uu____12500 =
                                             do_unify e ty1 ty2  in
                                           let uu____12504 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12500 uu____12504)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12407
=======
        let uu____12412 =
          bind get
            (fun ps  ->
               let uu____12420 = __tc e t1  in
               bind uu____12420
                 (fun uu____12441  ->
                    match uu____12441 with
                    | (t11,ty1,g1) ->
                        let uu____12454 = __tc e t2  in
                        bind uu____12454
                          (fun uu____12475  ->
                             match uu____12475 with
                             | (t21,ty2,g2) ->
                                 let uu____12488 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12488
                                   (fun uu____12495  ->
                                      let uu____12496 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12496
                                        (fun uu____12504  ->
                                           let uu____12505 =
                                             do_unify e ty1 ty2  in
                                           let uu____12509 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12505 uu____12509)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12412
>>>>>>> snap
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
<<<<<<< HEAD
          (fun uu____12552  ->
             let uu____12553 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12553
=======
          (fun uu____12557  ->
             let uu____12558 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12558
>>>>>>> snap
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
<<<<<<< HEAD
        (fun uu____12587  ->
           let uu____12588 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12588)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12599 =
      mlog
        (fun uu____12604  ->
           let uu____12605 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12605)
        (fun uu____12610  ->
           let uu____12611 = cur_goal ()  in
           bind uu____12611
             (fun g  ->
                let uu____12617 =
                  let uu____12626 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12626 ty  in
                bind uu____12617
                  (fun uu____12638  ->
                     match uu____12638 with
                     | (ty1,uu____12648,guard) ->
                         let uu____12650 =
                           let uu____12653 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12653 guard  in
                         bind uu____12650
                           (fun uu____12657  ->
                              let uu____12658 =
                                let uu____12662 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12663 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12662 uu____12663 ty1  in
                              bind uu____12658
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12672 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12672
=======
        (fun uu____12592  ->
           let uu____12593 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12593)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12604 =
      mlog
        (fun uu____12609  ->
           let uu____12610 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12610)
        (fun uu____12615  ->
           let uu____12616 = cur_goal ()  in
           bind uu____12616
             (fun g  ->
                let uu____12622 =
                  let uu____12631 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12631 ty  in
                bind uu____12622
                  (fun uu____12643  ->
                     match uu____12643 with
                     | (ty1,uu____12653,guard) ->
                         let uu____12655 =
                           let uu____12658 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12658 guard  in
                         bind uu____12655
                           (fun uu____12662  ->
                              let uu____12663 =
                                let uu____12667 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12668 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12667 uu____12668 ty1  in
                              bind uu____12663
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12677 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12677
>>>>>>> snap
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
<<<<<<< HEAD
                                        let uu____12679 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12680 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12679
                                          uu____12680
                                         in
                                      let nty =
                                        let uu____12682 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12682 ty1  in
                                      let uu____12683 =
                                        let uu____12687 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12687 ng nty  in
                                      bind uu____12683
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12696 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12696
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12599
=======
                                        let uu____12684 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12685 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12684
                                          uu____12685
                                         in
                                      let nty =
                                        let uu____12687 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12687 ty1  in
                                      let uu____12688 =
                                        let uu____12692 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12692 ng nty  in
                                      bind uu____12688
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12701 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12701
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12604
>>>>>>> snap
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
<<<<<<< HEAD
    let uu____12770 =
      let uu____12779 = cur_goal ()  in
      bind uu____12779
        (fun g  ->
           let uu____12791 =
             let uu____12800 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12800 s_tm  in
           bind uu____12791
             (fun uu____12818  ->
                match uu____12818 with
                | (s_tm1,s_ty,guard) ->
<<<<<<< HEAD
                    let uu____12836 =
                      let uu____12839 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12839 guard  in
                    bind uu____12836
                      (fun uu____12852  ->
                         let uu____12853 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12853 with
                         | (h,args) ->
                             let uu____12898 =
                               let uu____12905 =
                                 let uu____12906 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12906.FStar_Syntax_Syntax.n  in
                               match uu____12905 with
=======
                    let uu____12827 =
                      let uu____12830 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12830 guard  in
                    bind uu____12827
                      (fun uu____12844  ->
=======
    let uu____12775 =
      let uu____12784 = cur_goal ()  in
      bind uu____12784
        (fun g  ->
           let uu____12796 =
             let uu____12805 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12805 s_tm  in
           bind uu____12796
             (fun uu____12823  ->
                match uu____12823 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12841 =
                      let uu____12844 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12844 guard  in
                    bind uu____12841
                      (fun uu____12858  ->
>>>>>>> snap
                         let s_ty1 =
                           let uu____12860 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant]
                             uu____12860 s_ty
                            in
                         let uu____12861 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____12861 with
                         | (h,args) ->
                             let uu____12906 =
                               let uu____12913 =
                                 let uu____12914 =
                                   FStar_Syntax_Subst.compress h  in
<<<<<<< HEAD
                                 uu____12900.FStar_Syntax_Syntax.n  in
                               match uu____12899 with
>>>>>>> snap
=======
                                 uu____12914.FStar_Syntax_Syntax.n  in
                               match uu____12913 with
>>>>>>> snap
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
<<<<<<< HEAD
<<<<<<< HEAD
                                      FStar_Syntax_Syntax.pos = uu____12921;
                                      FStar_Syntax_Syntax.vars = uu____12922;_},us)
                                   -> ret (fv, us)
                               | uu____12932 -> fail "type is not an fv"  in
                             bind uu____12898
                               (fun uu____12953  ->
                                  match uu____12953 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12969 =
                                        let uu____12972 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12972 t_lid
                                         in
                                      (match uu____12969 with
=======
                                      FStar_Syntax_Syntax.pos = uu____12915;
                                      FStar_Syntax_Syntax.vars = uu____12916;_},us)
=======
                                      FStar_Syntax_Syntax.pos = uu____12929;
                                      FStar_Syntax_Syntax.vars = uu____12930;_},us)
>>>>>>> snap
                                   -> ret (fv, us)
                               | uu____12940 -> fail "type is not an fv"  in
                             bind uu____12906
                               (fun uu____12961  ->
                                  match uu____12961 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12977 =
                                        let uu____12980 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12980 t_lid
                                         in
<<<<<<< HEAD
                                      (match uu____12963 with
>>>>>>> snap
=======
                                      (match uu____12977 with
>>>>>>> snap
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
<<<<<<< HEAD
                                                failwhen
                                                  ((FStar_List.length a_us)
                                                     <>
                                                     (FStar_List.length t_us))
                                                  "t_us don't match?"
                                                  (fun uu____13023  ->
                                                     let uu____13024 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____13024 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____13039 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____13067
                                                                  =
                                                                  let uu____13070
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13070
                                                                    c_lid
                                                                   in
                                                                match uu____13067
                                                                with
                                                                | FStar_Pervasives_Native.None
=======
                                                let erasable1 =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr
                                                   in
                                                let uu____13021 =
                                                  erasable1 &&
                                                    (let uu____13024 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____13024)
                                                   in
                                                failwhen uu____13021
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____13034  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____13047  ->
                                                          let uu____13048 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____13048
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____13063
                                                                =
                                                                mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____13091
                                                                    =
                                                                    let uu____13094
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13094
                                                                    c_lid  in
                                                                    match uu____13091
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13144
=======
                                                                    uu____13151
>>>>>>> snap
=======
                                                                    uu____13154
>>>>>>> snap
=======
                                                                    uu____13168
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13149
=======
                                                                    let uu____13156
>>>>>>> snap
=======
                                                                    let uu____13159
>>>>>>> snap
=======
                                                                    let uu____13173
>>>>>>> snap
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    match uu____13149
=======
                                                                    match uu____13156
>>>>>>> snap
=======
                                                                    match uu____13159
>>>>>>> snap
=======
                                                                    match uu____13173
>>>>>>> snap
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13172
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13172
=======
                                                                    let uu____13179
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13179
>>>>>>> snap
=======
                                                                    let uu____13182
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13182
>>>>>>> snap
=======
                                                                    let uu____13196
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13196
>>>>>>> snap
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13215
=======
                                                                    let uu____13222
>>>>>>> snap
=======
                                                                    let uu____13225
>>>>>>> snap
=======
                                                                    let uu____13239
>>>>>>> snap
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    (match uu____13215
=======
                                                                    (match uu____13222
>>>>>>> snap
=======
                                                                    (match uu____13225
>>>>>>> snap
=======
                                                                    (match uu____13239
>>>>>>> snap
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13288
                                                                    =
                                                                    let uu____13290
=======
                                                                    let uu____13295
                                                                    =
                                                                    let uu____13297
>>>>>>> snap
=======
                                                                    let uu____13298
                                                                    =
                                                                    let uu____13300
>>>>>>> snap
=======
                                                                    let uu____13312
                                                                    =
                                                                    let uu____13314
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13290
                                                                     in
                                                                    failwhen
                                                                    uu____13288
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13309
=======
                                                                    uu____13297
=======
                                                                    uu____13300
>>>>>>> snap
=======
                                                                    uu____13314
>>>>>>> snap
                                                                     in
                                                                    failwhen
                                                                    uu____13312
                                                                    "not total?"
                                                                    (fun
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13316
>>>>>>> snap
=======
                                                                    uu____13319
>>>>>>> snap
=======
                                                                    uu____13333
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu___5_13326
                                                                    =
                                                                    match uu___5_13326
=======
                                                                    uu___5_13333
                                                                    =
                                                                    match uu___5_13333
>>>>>>> snap
=======
                                                                    uu___5_13336
                                                                    =
                                                                    match uu___5_13336
>>>>>>> snap
=======
                                                                    uu___5_13350
                                                                    =
                                                                    match uu___5_13350
>>>>>>> snap
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13330)
                                                                    -> true
                                                                    | 
                                                                    uu____13333
                                                                    -> false
                                                                     in
                                                                    let uu____13337
=======
                                                                    uu____13337)
=======
                                                                    uu____13340)
>>>>>>> snap
=======
                                                                    uu____13354)
>>>>>>> snap
                                                                    -> true
                                                                    | 
                                                                    uu____13357
                                                                    -> false
                                                                     in
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13344
>>>>>>> snap
=======
                                                                    let uu____13347
>>>>>>> snap
=======
                                                                    let uu____13361
>>>>>>> snap
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    match uu____13337
=======
                                                                    match uu____13344
>>>>>>> snap
=======
                                                                    match uu____13347
>>>>>>> snap
=======
                                                                    match uu____13361
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13471
=======
                                                                    uu____13479
>>>>>>> snap
=======
                                                                    uu____13472
>>>>>>> snap
=======
                                                                    uu____13482
>>>>>>> snap
=======
                                                                    uu____13496
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13533
=======
                                                                    uu____13534
>>>>>>> snap
                                                                     ->
                                                                    match uu____13534
                                                                    with
                                                                    | 
<<<<<<< HEAD
                                                                    ((bv,uu____13553),
                                                                    (t,uu____13555))
=======
                                                                    uu____13541
=======
                                                                    uu____13544
>>>>>>> snap
=======
                                                                    uu____13558
>>>>>>> snap
                                                                     ->
                                                                    match uu____13558
                                                                    with
                                                                    | 
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    ((bv,uu____13561),
                                                                    (t,uu____13563))
>>>>>>> snap
=======
                                                                    ((bv,uu____13554),
                                                                    (t,uu____13556))
>>>>>>> snap
=======
                                                                    ((bv,uu____13564),
                                                                    (t,uu____13566))
>>>>>>> snap
=======
                                                                    ((bv,uu____13578),
                                                                    (t,uu____13580))
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13625
=======
                                                                    uu____13626
>>>>>>> snap
                                                                     ->
                                                                    match uu____13626
                                                                    with
                                                                    | 
<<<<<<< HEAD
                                                                    ((bv,uu____13652),
                                                                    (t,uu____13654))
=======
                                                                    uu____13633
=======
                                                                    uu____13636
>>>>>>> snap
=======
                                                                    uu____13650
>>>>>>> snap
                                                                     ->
                                                                    match uu____13650
                                                                    with
                                                                    | 
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    ((bv,uu____13660),
                                                                    (t,uu____13662))
>>>>>>> snap
=======
                                                                    ((bv,uu____13653),
                                                                    (t,uu____13655))
>>>>>>> snap
=======
                                                                    ((bv,uu____13663),
                                                                    (t,uu____13665))
>>>>>>> snap
=======
                                                                    ((bv,uu____13677),
                                                                    (t,uu____13679))
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13713
                                                                     ->
                                                                    match uu____13713
=======
                                                                    uu____13721
                                                                     ->
                                                                    match uu____13721
>>>>>>> snap
=======
                                                                    uu____13714
                                                                     ->
                                                                    match uu____13714
>>>>>>> snap
=======
                                                                    uu____13724
                                                                     ->
                                                                    match uu____13724
>>>>>>> snap
=======
                                                                    uu____13738
                                                                     ->
                                                                    match uu____13738
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13768
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1891_13785
=======
                                                                    let uu____13776
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1893_13796
>>>>>>> snap
=======
                                                                    let uu____13769
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1891_13790
>>>>>>> snap
=======
                                                                    let uu____13779
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1894_13799
>>>>>>> snap
=======
                                                                    let uu____13793
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1895_13813
>>>>>>> snap
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    (uu___1891_13785.FStar_TypeChecker_Env.solver);
=======
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.solver);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1891_13785.FStar_TypeChecker_Env.admit);
=======
                                                                    (uu___1893_13796.FStar_TypeChecker_Env.solver);
=======
                                                                    (uu___1894_13799.FStar_TypeChecker_Env.solver);
>>>>>>> snap
=======
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.solver);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    (uu___1893_13796.FStar_TypeChecker_Env.admit);
>>>>>>> snap
=======
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.admit);
>>>>>>> snap
=======
                                                                    (uu___1894_13799.FStar_TypeChecker_Env.admit);
>>>>>>> snap
=======
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.admit);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    (uu___1891_13785.FStar_TypeChecker_Env.lax_universes);
=======
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.lax_universes);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
<<<<<<< HEAD
                                                                    (uu___1891_13785.FStar_TypeChecker_Env.synth_hook);
=======
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1891_13790.FStar_TypeChecker_Env.strict_args_tab)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13769
                                                                    with
                                                                    | 
                                                                    (uu____13804,uu____13805,uu____13806,uu____13807,pat_t,uu____13809,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13820
                                                                    =
<<<<<<< HEAD
                                                                    let uu____13811
=======
                                                                    (uu___1893_13796.FStar_TypeChecker_Env.lax_universes);
=======
                                                                    (uu___1894_13799.FStar_TypeChecker_Env.lax_universes);
>>>>>>> snap
=======
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.lax_universes);
>>>>>>> snap
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1895_13813.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____13793
                                                                    with
                                                                    | 
                                                                    (uu____13827,uu____13828,uu____13829,pat_t,uu____13831,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13841
                                                                    =
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13825
>>>>>>> snap
=======
                                                                    let uu____13821
>>>>>>> snap
=======
                                                                    let uu____13828
>>>>>>> snap
=======
                                                                    let uu____13842
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13811
=======
                                                                    uu____13825
>>>>>>> snap
=======
                                                                    uu____13821
>>>>>>> snap
=======
                                                                    uu____13828
>>>>>>> snap
=======
                                                                    uu____13842
>>>>>>> snap
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13810
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13816
=======
                                                                    uu____13824
=======
                                                                    uu____13827
>>>>>>> snap
=======
                                                                    uu____13841
>>>>>>> snap
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13847
                                                                    =
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13839
>>>>>>> snap
=======
                                                                    uu____13820
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13826
>>>>>>> snap
                                                                    =
                                                                    let uu____13835
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    [uu____13825]
                                                                     in
                                                                    let uu____13844
=======
                                                                    [uu____13839]
                                                                     in
                                                                    let uu____13858
>>>>>>> snap
=======
                                                                    [uu____13835]
                                                                     in
                                                                    let uu____13854
>>>>>>> snap
=======
                                                                    let uu____13842
=======
                                                                    let uu____13856
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13856]
                                                                     in
<<<<<<< HEAD
                                                                    let uu____13861
>>>>>>> snap
=======
                                                                    let uu____13875
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13816
                                                                    uu____13844
                                                                     in
                                                                    let nty =
                                                                    let uu____13850
=======
                                                                    uu____13830
                                                                    uu____13858
                                                                     in
                                                                    let nty =
                                                                    let uu____13864
>>>>>>> snap
=======
                                                                    uu____13826
                                                                    uu____13854
                                                                     in
                                                                    let nty =
                                                                    let uu____13860
>>>>>>> snap
=======
                                                                    uu____13833
                                                                    uu____13861
                                                                     in
                                                                    let nty =
                                                                    let uu____13867
>>>>>>> snap
=======
                                                                    uu____13847
                                                                    uu____13875
                                                                     in
                                                                    let nty =
                                                                    let uu____13881
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13850
                                                                     in
                                                                    let uu____13853
=======
                                                                    uu____13864
                                                                     in
                                                                    let uu____13867
>>>>>>> snap
=======
                                                                    uu____13860
                                                                     in
                                                                    let uu____13863
>>>>>>> snap
=======
                                                                    uu____13867
                                                                     in
                                                                    let uu____13870
>>>>>>> snap
=======
                                                                    uu____13881
                                                                     in
                                                                    let uu____13884
>>>>>>> snap
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13853
=======
                                                                    uu____13863
>>>>>>> snap
                                                                    (fun
                                                                    uu____13893
                                                                     ->
<<<<<<< HEAD
                                                                    match uu____13883
=======
                                                                    uu____13867
=======
                                                                    uu____13870
>>>>>>> snap
=======
                                                                    uu____13884
>>>>>>> snap
                                                                    (fun
                                                                    uu____13914
                                                                     ->
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    match uu____13897
>>>>>>> snap
=======
                                                                    match uu____13893
>>>>>>> snap
=======
                                                                    match uu____13900
>>>>>>> snap
=======
                                                                    match uu____13914
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13910
                                                                    =
                                                                    let uu____13921
=======
                                                                    let uu____13924
                                                                    =
                                                                    let uu____13935
>>>>>>> snap
=======
                                                                    let uu____13920
                                                                    =
                                                                    let uu____13931
>>>>>>> snap
=======
                                                                    let uu____13927
                                                                    =
                                                                    let uu____13938
>>>>>>> snap
=======
                                                                    let uu____13941
                                                                    =
                                                                    let uu____13952
>>>>>>> snap
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    [uu____13921]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13910
=======
                                                                    [uu____13935]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13924
>>>>>>> snap
=======
                                                                    [uu____13931]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13920
>>>>>>> snap
=======
                                                                    [uu____13938]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13927
>>>>>>> snap
=======
                                                                    [uu____13952]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13941
>>>>>>> snap
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13957
=======
                                                                    let uu____13967
>>>>>>> snap
                                                                    =
                                                                    let uu____13978
                                                                    =
<<<<<<< HEAD
                                                                    let uu____13973
=======
                                                                    let uu____13971
=======
                                                                    let uu____13974
>>>>>>> snap
=======
                                                                    let uu____13988
>>>>>>> snap
                                                                    =
                                                                    let uu____13999
                                                                    =
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____13987
>>>>>>> snap
=======
                                                                    let uu____13983
>>>>>>> snap
=======
                                                                    let uu____13990
>>>>>>> snap
=======
                                                                    let uu____14004
>>>>>>> snap
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____13973)
=======
                                                                    uu____13983)
>>>>>>> snap
                                                                     in
                                                                    (g', br,
                                                                    uu____13978)
                                                                     in
                                                                    ret
                                                                    uu____13967))))))
                                                                    | 
                                                                    uu____14004
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____13039
                                                           (fun goal_brs  ->
                                                              let uu____14054
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____14054
                                                              with
                                                              | (goals,brs,infos)
                                                                  ->
                                                                  let w =
=======
                                                                    uu____13987)
=======
                                                                    uu____13990)
>>>>>>> snap
=======
                                                                    uu____14004)
>>>>>>> snap
                                                                     in
                                                                    (g', br,
                                                                    uu____13999)
                                                                     in
                                                                    ret
                                                                    uu____13988))))))
                                                                    | 
                                                                    uu____14025
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              bind
                                                                uu____13063
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____14075
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____14075
                                                                   with
                                                                   | 
                                                                   (goals,brs,infos)
                                                                    ->
                                                                    let w =
>>>>>>> snap
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                  let uu____14117
=======
                                                                  let uu____14127
>>>>>>> snap
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____14127
                                                                    (
                                                                    fun
                                                                    uu____14138
                                                                     ->
<<<<<<< HEAD
                                                                    let uu____14129
=======
                                                                    let uu____14131
=======
                                                                    let uu____14134
>>>>>>> snap
=======
                                                                    let uu____14148
>>>>>>> snap
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    bind
                                                                    uu____14148
                                                                    (fun
                                                                    uu____14159
                                                                     ->
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    let uu____14143
>>>>>>> snap
=======
                                                                    let uu____14139
>>>>>>> snap
=======
                                                                    let uu____14146
>>>>>>> snap
=======
                                                                    let uu____14160
>>>>>>> snap
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                                                    uu____14129
                                                                    (fun
=======
>>>>>>> snap
                                                                    uu____14139
                                                                    (fun
                                                                    uu____14149
                                                                     ->
                                                                    ret infos))))
<<<<<<< HEAD
                                            | uu____14146 ->
=======
                                                                    uu____14143
=======
                                                                    uu____14146
>>>>>>> snap
=======
                                                                    uu____14160
>>>>>>> snap
                                                                    (fun
                                                                    uu____14170
                                                                     ->
                                                                    ret infos)))))
<<<<<<< HEAD
<<<<<<< HEAD
                                            | uu____14160 ->
>>>>>>> snap
=======
                                            | uu____14156 ->
>>>>>>> snap
=======
                                            | uu____14163 ->
>>>>>>> snap
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12770
=======
                                            | uu____14177 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12775
>>>>>>> snap
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____14195::xs -> last xs
=======
    | uu____14209::xs -> last xs
>>>>>>> snap
=======
    | uu____14205::xs -> last xs
>>>>>>> snap
=======
    | uu____14212::xs -> last xs
>>>>>>> snap
=======
    | uu____14226::xs -> last xs
>>>>>>> snap
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    | x::xs -> let uu____14225 = init xs  in x :: uu____14225
=======
    | x::xs -> let uu____14239 = init xs  in x :: uu____14239
>>>>>>> snap
=======
    | x::xs -> let uu____14235 = init xs  in x :: uu____14235
>>>>>>> snap
=======
    | x::xs -> let uu____14242 = init xs  in x :: uu____14242
>>>>>>> snap
=======
    | x::xs -> let uu____14256 = init xs  in x :: uu____14256
>>>>>>> snap
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____14238 =
=======
    let uu____14252 =
>>>>>>> snap
=======
    let uu____14248 =
>>>>>>> snap
=======
    let uu____14255 =
>>>>>>> snap
=======
    let uu____14269 =
>>>>>>> snap
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14247) -> inspect t4
=======
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14261) -> inspect t4
>>>>>>> snap
=======
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14257) -> inspect t4
>>>>>>> snap
=======
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14264) -> inspect t4
>>>>>>> snap
=======
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14278) -> inspect t4
>>>>>>> snap
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____14313 = last args  in
          (match uu____14313 with
=======
          let uu____14323 = last args  in
          (match uu____14323 with
>>>>>>> snap
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14353 =
                 let uu____14354 =
                   let uu____14359 =
                     let uu____14360 =
                       let uu____14365 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14365  in
                     uu____14360 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14359, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14354  in
               FStar_All.pipe_left ret uu____14353)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14376,uu____14377) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
<<<<<<< HEAD
          let uu____14420 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14420 with
=======
          let uu____14327 = last args  in
          (match uu____14327 with
=======
          let uu____14330 = last args  in
          (match uu____14330 with
>>>>>>> snap
=======
          let uu____14344 = last args  in
          (match uu____14344 with
>>>>>>> snap
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14374 =
                 let uu____14375 =
                   let uu____14380 =
                     let uu____14381 =
                       let uu____14386 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14386  in
                     uu____14381 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14380, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14375  in
               FStar_All.pipe_left ret uu____14374)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14397,uu____14398) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____14434 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14434 with
>>>>>>> snap
=======
          let uu____14430 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14430 with
>>>>>>> snap
=======
          let uu____14437 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14437 with
>>>>>>> snap
=======
          let uu____14451 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14451 with
>>>>>>> snap
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                    let uu____14462 =
                      let uu____14463 =
                        let uu____14468 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14468)  in
                      FStar_Reflection_Data.Tv_Abs uu____14463  in
                    FStar_All.pipe_left ret uu____14462))
      | FStar_Syntax_Syntax.Tm_type uu____14471 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14496 ->
          let uu____14511 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14511 with
=======
                    let uu____14476 =
                      let uu____14477 =
                        let uu____14482 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14482)  in
                      FStar_Reflection_Data.Tv_Abs uu____14477  in
                    FStar_All.pipe_left ret uu____14476))
      | FStar_Syntax_Syntax.Tm_type uu____14485 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14510 ->
          let uu____14525 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14525 with
>>>>>>> snap
=======
                    let uu____14472 =
                      let uu____14473 =
                        let uu____14478 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14478)  in
                      FStar_Reflection_Data.Tv_Abs uu____14473  in
                    FStar_All.pipe_left ret uu____14472))
      | FStar_Syntax_Syntax.Tm_type uu____14481 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14506 ->
          let uu____14521 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14521 with
>>>>>>> snap
=======
                    let uu____14479 =
                      let uu____14480 =
                        let uu____14485 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14485)  in
                      FStar_Reflection_Data.Tv_Abs uu____14480  in
                    FStar_All.pipe_left ret uu____14479))
      | FStar_Syntax_Syntax.Tm_type uu____14488 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14513 ->
          let uu____14528 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14528 with
>>>>>>> snap
=======
                    let uu____14493 =
                      let uu____14494 =
                        let uu____14499 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14499)  in
                      FStar_Reflection_Data.Tv_Abs uu____14494  in
                    FStar_All.pipe_left ret uu____14493))
      | FStar_Syntax_Syntax.Tm_type uu____14502 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14527 ->
          let uu____14542 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14542 with
>>>>>>> snap
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____14542 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14542 with
=======
          let uu____14556 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14556 with
>>>>>>> snap
=======
          let uu____14552 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14552 with
>>>>>>> snap
=======
          let uu____14559 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14559 with
>>>>>>> snap
=======
          let uu____14573 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14573 with
>>>>>>> snap
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 | uu____14595 -> failwith "impossible"  in
=======
                 | uu____14609 -> failwith "impossible"  in
>>>>>>> snap
=======
                 | uu____14605 -> failwith "impossible"  in
>>>>>>> snap
=======
                 | uu____14612 -> failwith "impossible"  in
>>>>>>> snap
=======
                 | uu____14626 -> failwith "impossible"  in
>>>>>>> snap
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____14608 =
            let uu____14609 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14609  in
          FStar_All.pipe_left ret uu____14608
=======
          let uu____14618 =
            let uu____14619 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14619  in
          FStar_All.pipe_left ret uu____14618
>>>>>>> snap
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14640 =
            let uu____14641 =
              let uu____14646 =
                let uu____14647 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
<<<<<<< HEAD
                FStar_BigInt.of_int_fs uu____14637  in
              (uu____14636, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14631  in
          FStar_All.pipe_left ret uu____14630
=======
          let uu____14622 =
            let uu____14623 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14623  in
          FStar_All.pipe_left ret uu____14622
=======
          let uu____14625 =
            let uu____14626 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14626  in
          FStar_All.pipe_left ret uu____14625
>>>>>>> snap
=======
          let uu____14639 =
            let uu____14640 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14640  in
          FStar_All.pipe_left ret uu____14639
>>>>>>> snap
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14661 =
            let uu____14662 =
              let uu____14667 =
                let uu____14668 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
<<<<<<< HEAD
<<<<<<< HEAD
                FStar_BigInt.of_int_fs uu____14651  in
              (uu____14650, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14645  in
          FStar_All.pipe_left ret uu____14644
>>>>>>> snap
=======
                FStar_BigInt.of_int_fs uu____14647  in
              (uu____14646, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14641  in
          FStar_All.pipe_left ret uu____14640
>>>>>>> snap
=======
                FStar_BigInt.of_int_fs uu____14654  in
              (uu____14653, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14648  in
          FStar_All.pipe_left ret uu____14647
>>>>>>> snap
=======
                FStar_BigInt.of_int_fs uu____14668  in
              (uu____14667, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14662  in
          FStar_All.pipe_left ret uu____14661
>>>>>>> snap
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             | FStar_Util.Inr uu____14677 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14682 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14682 with
=======
             | FStar_Util.Inr uu____14691 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14696 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14696 with
>>>>>>> snap
=======
             | FStar_Util.Inr uu____14687 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14692 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14692 with
>>>>>>> snap
=======
             | FStar_Util.Inr uu____14694 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14699 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14699 with
>>>>>>> snap
=======
             | FStar_Util.Inr uu____14708 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14713 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14713 with
>>>>>>> snap
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                        | uu____14735 ->
=======
                        | uu____14749 ->
>>>>>>> snap
=======
                        | uu____14745 ->
>>>>>>> snap
=======
                        | uu____14752 ->
>>>>>>> snap
=======
                        | uu____14766 ->
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             | FStar_Util.Inr uu____14777 ->
=======
             | FStar_Util.Inr uu____14787 ->
>>>>>>> snap
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14791 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
<<<<<<< HEAD
                 (match uu____14781 with
=======
             | FStar_Util.Inr uu____14791 ->
=======
             | FStar_Util.Inr uu____14794 ->
>>>>>>> snap
=======
             | FStar_Util.Inr uu____14808 ->
>>>>>>> snap
=======
             | FStar_Util.Inr uu____14810 ->
>>>>>>> snap
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14814 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 (match uu____14795 with
>>>>>>> snap
=======
                 (match uu____14791 with
>>>>>>> snap
=======
                 (match uu____14798 with
>>>>>>> snap
=======
                 (match uu____14812 with
>>>>>>> snap
=======
                 (match uu____14814 with
>>>>>>> snap
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                            | FStar_Util.Inr uu____14801 ->
=======
                            | FStar_Util.Inr uu____14815 ->
>>>>>>> snap
=======
                            | FStar_Util.Inr uu____14811 ->
>>>>>>> snap
=======
                            | FStar_Util.Inr uu____14818 ->
>>>>>>> snap
=======
                            | FStar_Util.Inr uu____14832 ->
>>>>>>> snap
=======
                            | FStar_Util.Inr uu____14834 ->
>>>>>>> snap
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
<<<<<<< HEAD
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                       | uu____14807 ->
=======
                       | uu____14821 ->
>>>>>>> snap
=======
                       | uu____14817 ->
>>>>>>> snap
=======
                       | uu____14824 ->
>>>>>>> snap
=======
                       | uu____14838 ->
>>>>>>> snap
=======
                                     (true,
                                       (lb1.FStar_Syntax_Syntax.lbattrs),
                                       bv1, (lb1.FStar_Syntax_Syntax.lbdef),
                                       t22)))
                       | uu____14842 ->
>>>>>>> snap
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                let uu____14862 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14862
=======
                let uu____14872 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14872
>>>>>>> snap
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14893 =
                  let uu____14900 =
                    FStar_List.map
                      (fun uu____14913  ->
                         match uu____14913 with
                         | (p1,uu____14922) -> inspect_pat p1) ps
                     in
<<<<<<< HEAD
                  (fv, uu____14890)  in
                FStar_Reflection_Data.Pat_Cons uu____14883
=======
                let uu____14876 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14876
=======
                let uu____14879 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14879
>>>>>>> snap
=======
                let uu____14893 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14893
>>>>>>> snap
=======
                let uu____14897 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14897
>>>>>>> snap
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14918 =
                  let uu____14930 =
                    FStar_List.map
                      (fun uu____14954  ->
                         match uu____14954 with
                         | (p1,b) ->
                             let uu____14975 = inspect_pat p1  in
                             (uu____14975, b)) ps
                     in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                  (fv, uu____14904)  in
                FStar_Reflection_Data.Pat_Cons uu____14897
>>>>>>> snap
=======
                  (fv, uu____14900)  in
                FStar_Reflection_Data.Pat_Cons uu____14893
>>>>>>> snap
=======
                  (fv, uu____14907)  in
=======
                  (fv, uu____14912)  in
>>>>>>> snap
                FStar_Reflection_Data.Pat_Cons uu____14900
>>>>>>> snap
=======
                  (fv, uu____14926)  in
                FStar_Reflection_Data.Pat_Cons uu____14914
>>>>>>> snap
=======
                  (fv, uu____14930)  in
                FStar_Reflection_Data.Pat_Cons uu____14918
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
              (fun uu___6_15008  ->
                 match uu___6_15008 with
                 | (pat,uu____15030,t5) ->
                     let uu____15048 = inspect_pat pat  in (uu____15048, t5))
=======
              (fun uu___6_15022  ->
                 match uu___6_15022 with
                 | (pat,uu____15044,t5) ->
                     let uu____15062 = inspect_pat pat  in (uu____15062, t5))
>>>>>>> snap
=======
              (fun uu___6_15018  ->
                 match uu___6_15018 with
                 | (pat,uu____15040,t5) ->
                     let uu____15058 = inspect_pat pat  in (uu____15058, t5))
>>>>>>> snap
=======
              (fun uu___6_15025  ->
                 match uu___6_15025 with
                 | (pat,uu____15047,t5) ->
                     let uu____15065 = inspect_pat pat  in (uu____15065, t5))
>>>>>>> snap
=======
              (fun uu___6_15053  ->
                 match uu___6_15053 with
                 | (pat,uu____15075,t5) ->
                     let uu____15093 = inspect_pat pat  in (uu____15093, t5))
>>>>>>> snap
=======
              (fun uu___6_15067  ->
                 match uu___6_15067 with
                 | (pat,uu____15089,t5) ->
                     let uu____15107 = inspect_pat pat  in (uu____15107, t5))
>>>>>>> snap
=======
              (fun uu___6_15071  ->
                 match uu___6_15071 with
                 | (pat,uu____15093,t5) ->
                     let uu____15111 = inspect_pat pat  in (uu____15111, t5))
>>>>>>> snap
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      | uu____15057 ->
          ((let uu____15059 =
              let uu____15065 =
                let uu____15067 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15069 = FStar_Syntax_Print.term_to_string t3  in
=======
      | uu____15067 ->
          ((let uu____15069 =
              let uu____15075 =
                let uu____15077 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15079 = FStar_Syntax_Print.term_to_string t3  in
>>>>>>> snap
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15077 uu____15079
                 in
              (FStar_Errors.Warning_CantInspect, uu____15075)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15069);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
<<<<<<< HEAD
    wrap_err "inspect" uu____14238
=======
      | uu____15071 ->
          ((let uu____15073 =
              let uu____15079 =
                let uu____15081 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15083 = FStar_Syntax_Print.term_to_string t3  in
=======
      | uu____15074 ->
          ((let uu____15076 =
              let uu____15082 =
                let uu____15084 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15086 = FStar_Syntax_Print.term_to_string t3  in
>>>>>>> snap
=======
      | uu____15102 ->
          ((let uu____15104 =
              let uu____15110 =
                let uu____15112 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15114 = FStar_Syntax_Print.term_to_string t3  in
>>>>>>> snap
=======
      | uu____15116 ->
          ((let uu____15118 =
              let uu____15124 =
                let uu____15126 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15128 = FStar_Syntax_Print.term_to_string t3  in
>>>>>>> snap
=======
      | uu____15120 ->
          ((let uu____15122 =
              let uu____15128 =
                let uu____15130 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15132 = FStar_Syntax_Print.term_to_string t3  in
>>>>>>> snap
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15130 uu____15132
                 in
              (FStar_Errors.Warning_CantInspect, uu____15128)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15122);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
<<<<<<< HEAD
<<<<<<< HEAD
    wrap_err "inspect" uu____14252
>>>>>>> snap
=======
    wrap_err "inspect" uu____14248
>>>>>>> snap
=======
    wrap_err "inspect" uu____14255
>>>>>>> snap
=======
    wrap_err "inspect" uu____14269
>>>>>>> snap
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____15087 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15087
=======
        let uu____15097 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15097
>>>>>>> snap
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15101 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15101
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15105 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15105
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15112 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15112
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15137 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15137
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15154 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15154
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15173 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15173
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15177 =
          let uu____15178 =
            let uu____15185 =
              let uu____15186 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15186  in
            FStar_Syntax_Syntax.mk uu____15185  in
          uu____15178 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15177
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15191 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
<<<<<<< HEAD
        FStar_All.pipe_left ret uu____15181
=======
        let uu____15101 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15101
=======
        let uu____15104 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15104
>>>>>>> snap
=======
        let uu____15132 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15132
>>>>>>> snap
=======
        let uu____15146 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15146
>>>>>>> snap
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15150 = FStar_Syntax_Syntax.bv_to_tm bv  in
=======
        let uu____15150 = FStar_Syntax_Syntax.bv_to_name bv  in
>>>>>>> snap
        FStar_All.pipe_left ret uu____15150
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15154 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15154
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15158 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15158
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15165 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15165
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15190 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15190
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15207 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15207
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15226 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15226
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15230 =
          let uu____15231 =
            let uu____15238 =
              let uu____15239 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15239  in
            FStar_Syntax_Syntax.mk uu____15238  in
          uu____15231 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15230
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15244 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        FStar_All.pipe_left ret uu____15195
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15191
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15198
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15226
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15240
>>>>>>> snap
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
=======
        FStar_All.pipe_left ret uu____15244
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
>>>>>>> snap
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____15192 =
          let uu____15193 =
            let uu____15200 =
              let uu____15201 =
                let uu____15215 =
                  let uu____15218 =
                    let uu____15219 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15219]  in
                  FStar_Syntax_Subst.close uu____15218 t2  in
                ((false, [lb]), uu____15215)  in
              FStar_Syntax_Syntax.Tm_let uu____15201  in
            FStar_Syntax_Syntax.mk uu____15200  in
          uu____15193 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15192
=======
        let uu____15206 =
          let uu____15207 =
            let uu____15214 =
              let uu____15215 =
                let uu____15229 =
                  let uu____15232 =
                    let uu____15233 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15233]  in
                  FStar_Syntax_Subst.close uu____15232 t2  in
                ((false, [lb]), uu____15229)  in
              FStar_Syntax_Syntax.Tm_let uu____15215  in
            FStar_Syntax_Syntax.mk uu____15214  in
          uu____15207 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15206
>>>>>>> snap
=======
        let uu____15202 =
          let uu____15203 =
            let uu____15210 =
              let uu____15211 =
                let uu____15225 =
                  let uu____15228 =
                    let uu____15229 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15229]  in
                  FStar_Syntax_Subst.close uu____15228 t2  in
                ((false, [lb]), uu____15225)  in
              FStar_Syntax_Syntax.Tm_let uu____15211  in
            FStar_Syntax_Syntax.mk uu____15210  in
          uu____15203 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15202
>>>>>>> snap
=======
        let uu____15209 =
          let uu____15210 =
            let uu____15217 =
              let uu____15218 =
                let uu____15232 =
                  let uu____15235 =
                    let uu____15236 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15236]  in
                  FStar_Syntax_Subst.close uu____15235 t2  in
                ((false, [lb]), uu____15232)  in
              FStar_Syntax_Syntax.Tm_let uu____15218  in
            FStar_Syntax_Syntax.mk uu____15217  in
          uu____15210 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15209
>>>>>>> snap
=======
        let uu____15237 =
          let uu____15238 =
            let uu____15245 =
              let uu____15246 =
                let uu____15260 =
                  let uu____15263 =
                    let uu____15264 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15264]  in
                  FStar_Syntax_Subst.close uu____15263 t2  in
                ((false, [lb]), uu____15260)  in
              FStar_Syntax_Syntax.Tm_let uu____15246  in
            FStar_Syntax_Syntax.mk uu____15245  in
          uu____15238 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15237
>>>>>>> snap
=======
        let uu____15251 =
          let uu____15252 =
            let uu____15259 =
              let uu____15260 =
                let uu____15274 =
                  let uu____15277 =
                    let uu____15278 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15278]  in
                  FStar_Syntax_Subst.close uu____15277 t2  in
                ((false, [lb]), uu____15274)  in
              FStar_Syntax_Syntax.Tm_let uu____15260  in
            FStar_Syntax_Syntax.mk uu____15259  in
          uu____15252 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15251
>>>>>>> snap
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
=======
        let uu____15258 =
          let uu____15259 =
            let uu____15266 =
              let uu____15267 =
                let uu____15281 =
                  let uu____15284 =
                    let uu____15285 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15285]  in
                  FStar_Syntax_Subst.close uu____15284 t2  in
                ((false, [lb]), uu____15281)  in
              FStar_Syntax_Syntax.Tm_let uu____15267  in
            FStar_Syntax_Syntax.mk uu____15266  in
          uu____15259 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15258
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
>>>>>>> snap
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____15261 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15261 with
         | (lbs,body) ->
             let uu____15276 =
=======
        let uu____15275 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15275 with
         | (lbs,body) ->
             let uu____15290 =
>>>>>>> snap
=======
        let uu____15271 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15271 with
         | (lbs,body) ->
             let uu____15286 =
>>>>>>> snap
=======
        let uu____15278 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15278 with
         | (lbs,body) ->
             let uu____15293 =
>>>>>>> snap
=======
        let uu____15306 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15306 with
         | (lbs,body) ->
             let uu____15321 =
>>>>>>> snap
=======
        let uu____15320 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15320 with
         | (lbs,body) ->
             let uu____15335 =
>>>>>>> snap
=======
        let uu____15330 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15330 with
         | (lbs,body) ->
             let uu____15345 =
>>>>>>> snap
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             FStar_All.pipe_left ret uu____15276)
=======
             FStar_All.pipe_left ret uu____15290)
>>>>>>> snap
=======
             FStar_All.pipe_left ret uu____15286)
>>>>>>> snap
=======
             FStar_All.pipe_left ret uu____15293)
>>>>>>> snap
=======
             FStar_All.pipe_left ret uu____15321)
>>>>>>> snap
=======
             FStar_All.pipe_left ret uu____15335)
>>>>>>> snap
=======
             FStar_All.pipe_left ret uu____15345)
>>>>>>> snap
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____15313 =
                let uu____15314 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15314  in
              FStar_All.pipe_left wrap uu____15313
=======
              let uu____15323 =
                let uu____15324 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15324  in
              FStar_All.pipe_left wrap uu____15323
>>>>>>> snap
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15331 =
                let uu____15332 =
                  let uu____15346 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15364 = pack_pat p1  in
                         (uu____15364, false)) ps
                     in
<<<<<<< HEAD
                  (fv, uu____15336)  in
                FStar_Syntax_Syntax.Pat_cons uu____15322  in
              FStar_All.pipe_left wrap uu____15321
=======
              let uu____15327 =
                let uu____15328 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15328  in
              FStar_All.pipe_left wrap uu____15327
=======
              let uu____15330 =
                let uu____15331 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15331  in
              FStar_All.pipe_left wrap uu____15330
>>>>>>> snap
=======
              let uu____15358 =
                let uu____15359 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15359  in
              FStar_All.pipe_left wrap uu____15358
>>>>>>> snap
=======
              let uu____15372 =
                let uu____15373 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15373  in
              FStar_All.pipe_left wrap uu____15372
>>>>>>> snap
=======
              let uu____15382 =
                let uu____15383 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15383  in
              FStar_All.pipe_left wrap uu____15382
>>>>>>> snap
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15400 =
                let uu____15401 =
                  let uu____15415 =
                    FStar_List.map
                      (fun uu____15439  ->
                         match uu____15439 with
                         | (p1,b) ->
                             let uu____15454 = pack_pat p1  in
                             (uu____15454, b)) ps
                     in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                  (fv, uu____15350)  in
                FStar_Syntax_Syntax.Pat_cons uu____15336  in
              FStar_All.pipe_left wrap uu____15335
>>>>>>> snap
=======
                  (fv, uu____15346)  in
                FStar_Syntax_Syntax.Pat_cons uu____15332  in
              FStar_All.pipe_left wrap uu____15331
>>>>>>> snap
=======
                  (fv, uu____15353)  in
                FStar_Syntax_Syntax.Pat_cons uu____15339  in
              FStar_All.pipe_left wrap uu____15338
>>>>>>> snap
=======
                  (fv, uu____15391)  in
                FStar_Syntax_Syntax.Pat_cons uu____15377  in
              FStar_All.pipe_left wrap uu____15376
>>>>>>> snap
=======
                  (fv, uu____15405)  in
                FStar_Syntax_Syntax.Pat_cons uu____15391  in
              FStar_All.pipe_left wrap uu____15390
>>>>>>> snap
=======
                  (fv, uu____15415)  in
                FStar_Syntax_Syntax.Pat_cons uu____15401  in
              FStar_All.pipe_left wrap uu____15400
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
            (fun uu___7_15403  ->
               match uu___7_15403 with
=======
            (fun uu___7_15413  ->
               match uu___7_15413 with
>>>>>>> snap
               | (pat,t1) ->
                   let uu____15430 = pack_pat pat  in
                   (uu____15430, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15478 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15478
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
<<<<<<< HEAD
        let uu____15496 =
=======
            (fun uu___7_15417  ->
               match uu___7_15417 with
=======
            (fun uu___7_15420  ->
               match uu___7_15420 with
>>>>>>> snap
=======
            (fun uu___7_15478  ->
               match uu___7_15478 with
>>>>>>> snap
=======
            (fun uu___7_15492  ->
               match uu___7_15492 with
>>>>>>> snap
=======
            (fun uu___7_15502  ->
               match uu___7_15502 with
>>>>>>> snap
               | (pat,t1) ->
                   let uu____15519 = pack_pat pat  in
                   (uu____15519, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15567 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15567
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____15510 =
>>>>>>> snap
=======
        let uu____15506 =
>>>>>>> snap
=======
        let uu____15513 =
>>>>>>> snap
=======
        let uu____15571 =
>>>>>>> snap
=======
        let uu____15585 =
>>>>>>> snap
=======
        let uu____15595 =
>>>>>>> snap
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        FStar_All.pipe_left ret uu____15496
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15542 =
=======
        FStar_All.pipe_left ret uu____15510
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15556 =
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15506
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15552 =
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15513
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15559 =
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15571
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15617 =
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15585
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15631 =
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15595
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15641 =
>>>>>>> snap
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        FStar_All.pipe_left ret uu____15542
=======
        FStar_All.pipe_left ret uu____15552
>>>>>>> snap
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15591 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
<<<<<<< HEAD
        FStar_All.pipe_left ret uu____15581
=======
        FStar_All.pipe_left ret uu____15556
=======
        FStar_All.pipe_left ret uu____15559
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15617
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15631
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15641
>>>>>>> snap
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15680 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        FStar_All.pipe_left ret uu____15595
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15591
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15598
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15656
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15670
>>>>>>> snap
=======
        FStar_All.pipe_left ret uu____15680
>>>>>>> snap
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____15601 =
=======
      let uu____15611 =
>>>>>>> snap
        bind get
          (fun ps  ->
             let uu____15617 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15617 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
<<<<<<< HEAD
      FStar_All.pipe_left (wrap_err "lget") uu____15601
=======
      let uu____15615 =
=======
      let uu____15618 =
>>>>>>> snap
=======
      let uu____15676 =
>>>>>>> snap
=======
      let uu____15690 =
>>>>>>> snap
=======
      let uu____15700 =
>>>>>>> snap
        bind get
          (fun ps  ->
             let uu____15706 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15706 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      FStar_All.pipe_left (wrap_err "lget") uu____15615
>>>>>>> snap
=======
      FStar_All.pipe_left (wrap_err "lget") uu____15611
>>>>>>> snap
=======
      FStar_All.pipe_left (wrap_err "lget") uu____15618
>>>>>>> snap
=======
      FStar_All.pipe_left (wrap_err "lget") uu____15676
>>>>>>> snap
=======
      FStar_All.pipe_left (wrap_err "lget") uu____15690
>>>>>>> snap
=======
      FStar_All.pipe_left (wrap_err "lget") uu____15700
>>>>>>> snap
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____15641 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2189_15648 = ps  in
                 let uu____15649 =
=======
        let uu____15655 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2192_15662 = ps  in
                 let uu____15663 =
>>>>>>> snap
=======
        let uu____15651 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2190_15658 = ps  in
                 let uu____15659 =
>>>>>>> snap
=======
        let uu____15658 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2193_15665 = ps  in
                 let uu____15666 =
>>>>>>> snap
=======
        let uu____15716 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2195_15723 = ps  in
                 let uu____15724 =
>>>>>>> snap
=======
        let uu____15730 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2196_15737 = ps  in
                 let uu____15738 =
>>>>>>> snap
=======
        let uu____15740 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2198_15747 = ps  in
                 let uu____15748 =
>>>>>>> snap
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                     (uu___2189_15648.FStar_Tactics_Types.main_context);
=======
                     (uu___2190_15658.FStar_Tactics_Types.main_context);
>>>>>>> snap
                   FStar_Tactics_Types.main_goal =
                     (uu___2190_15658.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2190_15658.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2190_15658.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2190_15658.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2190_15658.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2190_15658.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2190_15658.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2190_15658.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2190_15658.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2190_15658.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2190_15658.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15659
                 }  in
               set ps1)
           in
<<<<<<< HEAD
        FStar_All.pipe_left (wrap_err "lset") uu____15641
=======
                     (uu___2192_15662.FStar_Tactics_Types.main_context);
=======
                     (uu___2193_15665.FStar_Tactics_Types.main_context);
>>>>>>> snap
=======
                     (uu___2195_15723.FStar_Tactics_Types.main_context);
>>>>>>> snap
=======
                     (uu___2196_15737.FStar_Tactics_Types.main_context);
>>>>>>> snap
=======
                     (uu___2198_15747.FStar_Tactics_Types.main_context);
<<<<<<< HEAD
>>>>>>> snap
                   FStar_Tactics_Types.main_goal =
                     (uu___2198_15747.FStar_Tactics_Types.main_goal);
=======
>>>>>>> snap
                   FStar_Tactics_Types.all_implicits =
                     (uu___2198_15747.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2198_15747.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2198_15747.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2198_15747.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2198_15747.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2198_15747.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2198_15747.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2198_15747.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2198_15747.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2198_15747.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15748
                 }  in
               set ps1)
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        FStar_All.pipe_left (wrap_err "lset") uu____15655
>>>>>>> snap
=======
        FStar_All.pipe_left (wrap_err "lset") uu____15651
>>>>>>> snap
=======
        FStar_All.pipe_left (wrap_err "lset") uu____15658
>>>>>>> snap
=======
        FStar_All.pipe_left (wrap_err "lset") uu____15716
>>>>>>> snap
=======
        FStar_All.pipe_left (wrap_err "lset") uu____15730
>>>>>>> snap
=======
        FStar_All.pipe_left (wrap_err "lset") uu____15740
>>>>>>> snap
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____15676 =
=======
      let uu____15686 =
>>>>>>> snap
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15686 with
      | (u,ctx_uvars,g_u) ->
          let uu____15719 = FStar_List.hd ctx_uvars  in
          (match uu____15719 with
           | (ctx_uvar,uu____15733) ->
               let g =
<<<<<<< HEAD
                 let uu____15725 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15725 false
=======
      let uu____15690 =
=======
      let uu____15693 =
>>>>>>> snap
=======
      let uu____15751 =
>>>>>>> snap
=======
      let uu____15765 =
>>>>>>> snap
=======
      let uu____15775 =
>>>>>>> snap
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15775 with
      | (u,ctx_uvars,g_u) ->
          let uu____15808 = FStar_List.hd ctx_uvars  in
          (match uu____15808 with
           | (ctx_uvar,uu____15822) ->
               let g =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 let uu____15739 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15739 false
>>>>>>> snap
=======
                 let uu____15735 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15735 false
>>>>>>> snap
=======
                 let uu____15742 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15742 false
>>>>>>> snap
=======
                 let uu____15800 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15800 false
>>>>>>> snap
=======
                 let uu____15814 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15814 false
>>>>>>> snap
=======
                 let uu____15824 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15824 false
>>>>>>> snap
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____15833 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____15833 with
    | (env1,uu____15841) ->
        let env2 =
          let uu___2215_15847 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2215_15847.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2215_15847.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2215_15847.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2215_15847.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2215_15847.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2215_15847.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2215_15847.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2215_15847.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2215_15847.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2215_15847.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___2215_15847.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2215_15847.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2215_15847.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2215_15847.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2215_15847.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2215_15847.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2215_15847.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2215_15847.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2215_15847.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2215_15847.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2215_15847.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2215_15847.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2215_15847.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2215_15847.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2215_15847.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2215_15847.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2215_15847.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2215_15847.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2215_15847.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2215_15847.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2215_15847.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2215_15847.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2215_15847.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2215_15847.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2215_15847.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2215_15847.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2215_15847.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2215_15847.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2215_15847.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2215_15847.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2215_15847.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2215_15847.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2215_15847.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2215_15847.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env3 =
          let uu___2218_15850 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2218_15850.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2218_15850.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2218_15850.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2218_15850.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2218_15850.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2218_15850.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2218_15850.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2218_15850.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2218_15850.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2218_15850.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2218_15850.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2218_15850.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2218_15850.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2218_15850.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2218_15850.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2218_15850.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2218_15850.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2218_15850.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2218_15850.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2218_15850.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2218_15850.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2218_15850.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___2218_15850.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2218_15850.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2218_15850.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2218_15850.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2218_15850.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2218_15850.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2218_15850.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2218_15850.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2218_15850.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2218_15850.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2218_15850.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2218_15850.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2218_15850.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2218_15850.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2218_15850.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2218_15850.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2218_15850.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2218_15850.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2218_15850.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2218_15850.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2218_15850.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2218_15850.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env4 =
          let uu___2221_15853 = env3  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2221_15853.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2221_15853.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2221_15853.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2221_15853.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2221_15853.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2221_15853.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2221_15853.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2221_15853.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2221_15853.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2221_15853.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2221_15853.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2221_15853.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2221_15853.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2221_15853.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2221_15853.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2221_15853.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2221_15853.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2221_15853.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2221_15853.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2221_15853.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2221_15853.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2221_15853.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2221_15853.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2221_15853.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2221_15853.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2221_15853.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2221_15853.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2221_15853.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2221_15853.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2221_15853.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2221_15853.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2221_15853.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2221_15853.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2221_15853.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2221_15853.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2221_15853.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2221_15853.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2221_15853.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2221_15853.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2221_15853.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2221_15853.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2221_15853.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2221_15853.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2221_15853.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        env4
  
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Env.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng  ->
    fun env  ->
      fun goals  ->
        fun imps  ->
          let env1 = tac_env env  in
          let ps =
            let uu____15886 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____15889 = FStar_Util.psmap_empty ()  in
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
              FStar_Tactics_Types.tac_verb_dbg = uu____15886;
              FStar_Tactics_Types.local_state = uu____15889
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____15748 = goal_of_goal_ty env typ  in
        match uu____15748 with
=======
        let uu____15758 = goal_of_goal_ty env typ  in
        match uu____15758 with
>>>>>>> snap
        | (g,g_u) ->
            let ps =
              let uu____15770 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
<<<<<<< HEAD
              let uu____15763 = FStar_Util.psmap_empty ()  in
=======
        let uu____15762 = goal_of_goal_ty env typ  in
        match uu____15762 with
=======
        let uu____15765 = goal_of_goal_ty env typ  in
        match uu____15765 with
>>>>>>> snap
=======
        let uu____15823 = goal_of_goal_ty env typ  in
        match uu____15823 with
>>>>>>> snap
=======
        let uu____15837 = goal_of_goal_ty env typ  in
        match uu____15837 with
>>>>>>> snap
=======
        let uu____15847 = goal_of_goal_ty env typ  in
        match uu____15847 with
>>>>>>> snap
        | (g,g_u) ->
            let ps =
              let uu____15859 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____15777 = FStar_Util.psmap_empty ()  in
>>>>>>> snap
=======
              let uu____15773 = FStar_Util.psmap_empty ()  in
>>>>>>> snap
=======
              let uu____15780 = FStar_Util.psmap_empty ()  in
>>>>>>> snap
=======
              let uu____15838 = FStar_Util.psmap_empty ()  in
>>>>>>> snap
=======
              let uu____15852 = FStar_Util.psmap_empty ()  in
>>>>>>> snap
=======
              let uu____15862 = FStar_Util.psmap_empty ()  in
>>>>>>> snap
              {
                FStar_Tactics_Types.main_context = env;
                FStar_Tactics_Types.main_goal = g;
                FStar_Tactics_Types.all_implicits =
                  (g_u.FStar_TypeChecker_Common.implicits);
                FStar_Tactics_Types.goals = [g];
                FStar_Tactics_Types.smt_goals = [];
                FStar_Tactics_Types.depth = Prims.int_zero;
                FStar_Tactics_Types.__dump = do_dump_proofstate;
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = Prims.int_zero;
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                FStar_Tactics_Types.tac_verb_dbg = uu____15760;
                FStar_Tactics_Types.local_state = uu____15763
              }  in
            let uu____15768 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15768)
=======
                FStar_Tactics_Types.tac_verb_dbg = uu____15774;
                FStar_Tactics_Types.local_state = uu____15777
              }  in
            let uu____15782 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15782)
>>>>>>> snap
=======
                FStar_Tactics_Types.tac_verb_dbg = uu____15770;
                FStar_Tactics_Types.local_state = uu____15773
              }  in
            let uu____15778 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15778)
  
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env  ->
    fun i  ->
      let uu____15790 = FStar_Options.peek ()  in
      FStar_Tactics_Types.mk_goal env i.FStar_TypeChecker_Common.imp_uvar
        uu____15790 false ""
  
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun imps  ->
        let goals = FStar_List.map (goal_of_implicit env) imps  in
        let w =
          let uu____15817 = FStar_List.hd goals  in
          FStar_Tactics_Types.goal_witness uu____15817  in
        let ps =
          let uu____15819 = FStar_List.hd goals  in
          let uu____15820 =
            FStar_TypeChecker_Env.debug env
              (FStar_Options.Other "TacVerbose")
             in
          let uu____15823 = FStar_Util.psmap_empty ()  in
          {
            FStar_Tactics_Types.main_context = env;
            FStar_Tactics_Types.main_goal = uu____15819;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps  -> fun msg  -> do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____15820;
            FStar_Tactics_Types.local_state = uu____15823
          }  in
        (ps, w)
>>>>>>> snap
=======
                FStar_Tactics_Types.tac_verb_dbg = uu____15777;
                FStar_Tactics_Types.local_state = uu____15780
              }  in
            let uu____15785 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15785)
>>>>>>> snap
=======
                FStar_Tactics_Types.tac_verb_dbg = uu____15835;
                FStar_Tactics_Types.local_state = uu____15838
              }  in
            let uu____15843 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15843)
>>>>>>> snap
=======
                FStar_Tactics_Types.tac_verb_dbg = uu____15849;
                FStar_Tactics_Types.local_state = uu____15852
              }  in
            let uu____15857 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15857)
>>>>>>> snap
=======
                FStar_Tactics_Types.tac_verb_dbg = uu____15859;
                FStar_Tactics_Types.local_state = uu____15862
              }  in
            let uu____15867 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15867)
>>>>>>> snap
=======
        let env1 = tac_env env  in
        let uu____15915 = goal_of_goal_ty env1 typ  in
        match uu____15915 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Env.implicits
               in
            let uu____15927 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15927)
>>>>>>> snap
  