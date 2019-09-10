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
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
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
                   FStar_Tactics_Types.main_goal =
                     (uu___229_1715.FStar_Tactics_Types.main_goal);
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
              FStar_Tactics_Types.main_goal =
                (uu___290_1977.FStar_Tactics_Types.main_goal);
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
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
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
           FStar_TypeChecker_Env.guard_f =
             (uu___324_2099.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___324_2099.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___324_2099.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
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
           FStar_Tactics_Types.main_goal =
             (uu___328_2102.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
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
           FStar_Tactics_Types.main_goal =
             (uu___351_2226.FStar_Tactics_Types.main_goal);
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
           FStar_Tactics_Types.main_goal =
             (uu___364_2289.FStar_Tactics_Types.main_goal);
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
              FStar_Tactics_Types.main_goal =
                (uu___380_2391.FStar_Tactics_Types.main_goal);
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
              FStar_Tactics_Types.main_goal =
                (uu___384_2410.FStar_Tactics_Types.main_goal);
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
              FStar_Tactics_Types.main_goal =
                (uu___406_2595.FStar_Tactics_Types.main_goal);
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
              FStar_Tactics_Types.main_goal =
                (uu___411_2616.FStar_Tactics_Types.main_goal);
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
              FStar_Tactics_Types.main_goal =
                (uu___416_2637.FStar_Tactics_Types.main_goal);
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
              FStar_Tactics_Types.main_goal =
                (uu___421_2658.FStar_Tactics_Types.main_goal);
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
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
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
             FStar_Tactics_Types.main_goal =
               (uu___466_2934.FStar_Tactics_Types.main_goal);
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
              let uu____2980 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2980 phi  in
            let uu____2981 = new_uvar reason env typ  in
            bind uu____2981
              (fun uu____2996  ->
                 match uu____2996 with
                 | (uu____3003,ctx_uvar) ->
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
             (fun uu____3050  ->
                let uu____3051 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3051)
             (fun uu____3056  ->
                let e1 =
                  let uu___484_3058 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___484_3058.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___484_3058.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___484_3058.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___484_3058.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___484_3058.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___484_3058.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___484_3058.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___484_3058.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___484_3058.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___484_3058.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___484_3058.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___484_3058.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___484_3058.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___484_3058.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___484_3058.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___484_3058.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___484_3058.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___484_3058.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___484_3058.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___484_3058.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___484_3058.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___484_3058.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___484_3058.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___484_3058.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___484_3058.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___484_3058.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___484_3058.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___484_3058.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___484_3058.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___484_3058.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___484_3058.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___484_3058.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___484_3058.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___484_3058.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___484_3058.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___484_3058.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___484_3058.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___484_3058.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___484_3058.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___484_3058.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___484_3058.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___484_3058.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                try
                  (fun uu___488_3070  ->
                     match () with
                     | () ->
                         let uu____3079 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3079) ()
                with
                | FStar_Errors.Err (uu____3106,msg) ->
                    let uu____3110 = tts e1 t  in
                    let uu____3112 =
                      let uu____3114 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3114
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3110 uu____3112 msg
                | FStar_Errors.Error (uu____3124,msg,uu____3126) ->
                    let uu____3129 = tts e1 t  in
                    let uu____3131 =
                      let uu____3133 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3133
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3129 uu____3131 msg))
  
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
             (fun uu____3186  ->
                let uu____3187 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3187)
             (fun uu____3192  ->
                let e1 =
                  let uu___505_3194 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___505_3194.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___505_3194.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___505_3194.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___505_3194.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___505_3194.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___505_3194.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___505_3194.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___505_3194.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___505_3194.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___505_3194.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___505_3194.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___505_3194.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___505_3194.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___505_3194.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___505_3194.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___505_3194.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___505_3194.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___505_3194.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___505_3194.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___505_3194.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___505_3194.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___505_3194.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___505_3194.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___505_3194.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___505_3194.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___505_3194.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___505_3194.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___505_3194.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___505_3194.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___505_3194.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___505_3194.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___505_3194.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___505_3194.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___505_3194.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___505_3194.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___505_3194.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___505_3194.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___505_3194.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___505_3194.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___505_3194.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___505_3194.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___505_3194.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                try
                  (fun uu___509_3209  ->
                     match () with
                     | () ->
                         let uu____3218 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3218 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3256,msg) ->
                    let uu____3260 = tts e1 t  in
                    let uu____3262 =
                      let uu____3264 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3264
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3260 uu____3262 msg
                | FStar_Errors.Error (uu____3274,msg,uu____3276) ->
                    let uu____3279 = tts e1 t  in
                    let uu____3281 =
                      let uu____3283 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3283
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3279 uu____3281 msg))
  
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
             (fun uu____3336  ->
                let uu____3337 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3337)
             (fun uu____3343  ->
                let e1 =
                  let uu___530_3345 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___530_3345.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___530_3345.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___530_3345.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___530_3345.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___530_3345.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___530_3345.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___530_3345.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___530_3345.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___530_3345.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___530_3345.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___530_3345.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___530_3345.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___530_3345.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___530_3345.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___530_3345.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___530_3345.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___530_3345.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___530_3345.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___530_3345.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___530_3345.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___530_3345.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___530_3345.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___530_3345.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___530_3345.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___530_3345.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___530_3345.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___530_3345.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___530_3345.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___530_3345.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___530_3345.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___530_3345.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___530_3345.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___530_3345.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___530_3345.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___530_3345.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___530_3345.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___530_3345.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___530_3345.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___530_3345.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___530_3345.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___530_3345.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___530_3345.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e2 =
                  let uu___533_3348 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___533_3348.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___533_3348.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___533_3348.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___533_3348.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___533_3348.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___533_3348.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___533_3348.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___533_3348.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___533_3348.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___533_3348.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___533_3348.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___533_3348.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___533_3348.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___533_3348.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___533_3348.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___533_3348.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___533_3348.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___533_3348.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___533_3348.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___533_3348.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___533_3348.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___533_3348.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___533_3348.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___533_3348.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___533_3348.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___533_3348.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___533_3348.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___533_3348.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___533_3348.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___533_3348.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___533_3348.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___533_3348.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___533_3348.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___533_3348.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___533_3348.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___533_3348.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___533_3348.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___533_3348.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___533_3348.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___533_3348.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___533_3348.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___533_3348.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                try
                  (fun uu___537_3360  ->
                     match () with
                     | () ->
                         let uu____3369 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3369) ()
                with
                | FStar_Errors.Err (uu____3396,msg) ->
                    let uu____3400 = tts e2 t  in
                    let uu____3402 =
                      let uu____3404 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3404
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3400 uu____3402 msg
                | FStar_Errors.Error (uu____3414,msg,uu____3416) ->
                    let uu____3419 = tts e2 t  in
                    let uu____3421 =
                      let uu____3423 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3423
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3419 uu____3421 msg))
  
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
  fun uu____3457  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___558_3476 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___558_3476.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___558_3476.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___558_3476.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___558_3476.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___558_3476.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___558_3476.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___558_3476.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___558_3476.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___558_3476.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___558_3476.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___558_3476.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___558_3476.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3501 = get_guard_policy ()  in
      bind uu____3501
        (fun old_pol  ->
           let uu____3507 = set_guard_policy pol  in
           bind uu____3507
             (fun uu____3511  ->
                bind t
                  (fun r  ->
                     let uu____3515 = set_guard_policy old_pol  in
                     bind uu____3515 (fun uu____3519  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3523 = let uu____3528 = cur_goal ()  in trytac uu____3528  in
  bind uu____3523
    (fun uu___0_3535  ->
       match uu___0_3535 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3541 = FStar_Options.peek ()  in ret uu____3541)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3566  ->
             let uu____3567 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3567)
          (fun uu____3572  ->
             let uu____3573 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3573
               (fun uu____3577  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3581 =
                         let uu____3582 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3582.FStar_TypeChecker_Env.guard_f  in
                       match uu____3581 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3586 = istrivial e f  in
                           if uu____3586
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3599 =
                                          let uu____3605 =
                                            let uu____3607 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3607
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3605)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3599);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3613  ->
                                           let uu____3614 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3614)
                                        (fun uu____3619  ->
                                           let uu____3620 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3620
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___587_3628 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___587_3628.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___587_3628.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___587_3628.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___587_3628.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3632  ->
                                           let uu____3633 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3633)
                                        (fun uu____3638  ->
                                           let uu____3639 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3639
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___594_3647 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___594_3647.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___594_3647.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___594_3647.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___594_3647.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3651  ->
                                           let uu____3652 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3652)
                                        (fun uu____3656  ->
                                           try
                                             (fun uu___601_3661  ->
                                                match () with
                                                | () ->
                                                    let uu____3664 =
                                                      let uu____3666 =
                                                        let uu____3668 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3668
                                                         in
                                                      Prims.op_Negation
                                                        uu____3666
                                                       in
                                                    if uu____3664
                                                    then
                                                      mlog
                                                        (fun uu____3675  ->
                                                           let uu____3676 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3676)
                                                        (fun uu____3680  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___600_3685 ->
                                               mlog
                                                 (fun uu____3690  ->
                                                    let uu____3691 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3691)
                                                 (fun uu____3695  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____3707 =
      let uu____3710 = cur_goal ()  in
      bind uu____3710
        (fun goal  ->
           let uu____3716 =
             let uu____3725 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3725 t  in
           bind uu____3716
             (fun uu____3737  ->
                match uu____3737 with
                | (uu____3746,lc,uu____3748) ->
                    let uu____3749 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____3749))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____3707
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3765 =
      let uu____3770 = tcc t  in
      bind uu____3770 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3765
  
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
            let uu____3822 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3822 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3834  ->
    let uu____3837 = cur_goal ()  in
    bind uu____3837
      (fun goal  ->
         let uu____3843 =
           let uu____3845 = FStar_Tactics_Types.goal_env goal  in
           let uu____3846 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3845 uu____3846  in
         if uu____3843
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3852 =
              let uu____3854 = FStar_Tactics_Types.goal_env goal  in
              let uu____3855 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3854 uu____3855  in
            fail1 "Not a trivial goal: %s" uu____3852))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3906 =
               try
                 (fun uu___659_3929  ->
                    match () with
                    | () ->
                        let uu____3940 =
                          let uu____3949 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3949
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3940) ()
               with | uu___658_3960 -> fail "divide: not enough goals"  in
             bind uu____3906
               (fun uu____3997  ->
                  match uu____3997 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___641_4023 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___641_4023.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___641_4023.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___641_4023.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___641_4023.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___641_4023.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___641_4023.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___641_4023.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___641_4023.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___641_4023.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___641_4023.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___641_4023.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4024 = set lp  in
                      bind uu____4024
                        (fun uu____4032  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___647_4048 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___647_4048.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___647_4048.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___647_4048.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___647_4048.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___647_4048.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___647_4048.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___647_4048.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___647_4048.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___647_4048.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___647_4048.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___647_4048.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4049 = set rp  in
                                     bind uu____4049
                                       (fun uu____4057  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___653_4073 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___653_4073.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___653_4073.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4074 = set p'
                                                       in
                                                    bind uu____4074
                                                      (fun uu____4082  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4088 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4110 = divide FStar_BigInt.one f idtac  in
    bind uu____4110
      (fun uu____4123  -> match uu____4123 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4161::uu____4162 ->
             let uu____4165 =
               let uu____4174 = map tau  in
               divide FStar_BigInt.one tau uu____4174  in
             bind uu____4165
               (fun uu____4192  ->
                  match uu____4192 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4234 =
        bind t1
          (fun uu____4239  ->
             let uu____4240 = map t2  in
             bind uu____4240 (fun uu____4248  -> ret ()))
         in
      focus uu____4234
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4258  ->
    let uu____4261 =
      let uu____4264 = cur_goal ()  in
      bind uu____4264
        (fun goal  ->
           let uu____4273 =
             let uu____4280 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4280  in
           match uu____4273 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4289 =
                 let uu____4291 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4291  in
               if uu____4289
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4300 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4300 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4316 = new_uvar "intro" env' typ'  in
                  bind uu____4316
                    (fun uu____4333  ->
                       match uu____4333 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4357 = set_solution goal sol  in
                           bind uu____4357
                             (fun uu____4363  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4365 =
                                  let uu____4368 = bnorm_goal g  in
                                  replace_cur uu____4368  in
                                bind uu____4365 (fun uu____4370  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4375 =
                 let uu____4377 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4378 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4377 uu____4378  in
               fail1 "goal is not an arrow (%s)" uu____4375)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4261
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4396  ->
    let uu____4403 = cur_goal ()  in
    bind uu____4403
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4422 =
            let uu____4429 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4429  in
          match uu____4422 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4442 =
                let uu____4444 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4444  in
              if uu____4442
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4461 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4461
                    in
                 let bs =
                   let uu____4472 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4472; b]  in
                 let env' =
                   let uu____4498 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4498 bs  in
                 let uu____4499 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4499
                   (fun uu____4525  ->
                      match uu____4525 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4539 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4542 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4539
                              FStar_Parser_Const.effect_Tot_lid uu____4542 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4560 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4560 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4582 =
                                   let uu____4583 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4583.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4582
                                  in
                               let uu____4599 = set_solution goal tm  in
                               bind uu____4599
                                 (fun uu____4608  ->
                                    let uu____4609 =
                                      let uu____4612 =
                                        bnorm_goal
                                          (let uu___724_4615 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___724_4615.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___724_4615.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___724_4615.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___724_4615.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4612  in
                                    bind uu____4609
                                      (fun uu____4622  ->
                                         let uu____4623 =
                                           let uu____4628 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4628, b)  in
                                         ret uu____4623)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4637 =
                let uu____4639 = FStar_Tactics_Types.goal_env goal  in
                let uu____4640 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4639 uu____4640  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4637))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4660 = cur_goal ()  in
    bind uu____4660
      (fun goal  ->
         mlog
           (fun uu____4667  ->
              let uu____4668 =
                let uu____4670 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4670  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4668)
           (fun uu____4676  ->
              let steps =
                let uu____4680 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4680
                 in
              let t =
                let uu____4684 = FStar_Tactics_Types.goal_env goal  in
                let uu____4685 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4684 uu____4685  in
              let uu____4686 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4686))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4711 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4719 -> g.FStar_Tactics_Types.opts
                 | uu____4722 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4727  ->
                    let uu____4728 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4728)
                 (fun uu____4733  ->
                    let uu____4734 = __tc_lax e t  in
                    bind uu____4734
                      (fun uu____4755  ->
                         match uu____4755 with
                         | (t1,uu____4765,uu____4766) ->
                             let steps =
                               let uu____4770 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4770
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4776  ->
                                  let uu____4777 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4777)
                               (fun uu____4781  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4711
  
let (refine_intro : unit -> unit tac) =
  fun uu____4794  ->
    let uu____4797 =
      let uu____4800 = cur_goal ()  in
      bind uu____4800
        (fun g  ->
           let uu____4807 =
             let uu____4818 = FStar_Tactics_Types.goal_env g  in
             let uu____4819 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4818 uu____4819
              in
           match uu____4807 with
           | (uu____4822,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4848 =
                 let uu____4853 =
                   let uu____4858 =
                     let uu____4859 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4859]  in
                   FStar_Syntax_Subst.open_term uu____4858 phi  in
                 match uu____4853 with
                 | (bvs,phi1) ->
                     let uu____4884 =
                       let uu____4885 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4885  in
                     (uu____4884, phi1)
                  in
               (match uu____4848 with
                | (bv1,phi1) ->
                    let uu____4904 =
                      let uu____4907 = FStar_Tactics_Types.goal_env g  in
                      let uu____4908 =
                        let uu____4909 =
                          let uu____4912 =
                            let uu____4913 =
                              let uu____4920 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4920)  in
                            FStar_Syntax_Syntax.NT uu____4913  in
                          [uu____4912]  in
                        FStar_Syntax_Subst.subst uu____4909 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4907
                        uu____4908 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4904
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4929  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4797
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4952 = cur_goal ()  in
      bind uu____4952
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4961 = FStar_Tactics_Types.goal_env goal  in
               let uu____4962 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4961 uu____4962
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4965 = __tc env t  in
           bind uu____4965
             (fun uu____4984  ->
                match uu____4984 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4999  ->
                         let uu____5000 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5002 =
                           let uu____5004 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5004
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____5000 uu____5002)
                      (fun uu____5008  ->
                         let uu____5009 =
                           let uu____5012 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5012 guard  in
                         bind uu____5009
                           (fun uu____5015  ->
                              mlog
                                (fun uu____5019  ->
                                   let uu____5020 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5022 =
                                     let uu____5024 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5024
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5020 uu____5022)
                                (fun uu____5028  ->
                                   let uu____5029 =
                                     let uu____5033 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5034 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5033 typ uu____5034  in
                                   bind uu____5029
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____5044 =
                                             let uu____5046 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5046 t1  in
                                           let uu____5047 =
                                             let uu____5049 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5049 typ  in
                                           let uu____5050 =
                                             let uu____5052 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5053 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____5052 uu____5053  in
                                           let uu____5054 =
                                             let uu____5056 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5057 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____5056 uu____5057  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____5044 uu____5047 uu____5050
                                             uu____5054)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5083 =
          mlog
            (fun uu____5088  ->
               let uu____5089 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5089)
            (fun uu____5094  ->
               let uu____5095 =
                 let uu____5102 = __exact_now set_expected_typ1 tm  in
                 catch uu____5102  in
               bind uu____5095
                 (fun uu___2_5111  ->
                    match uu___2_5111 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5122  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5126  ->
                             let uu____5127 =
                               let uu____5134 =
                                 let uu____5137 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5137
                                   (fun uu____5142  ->
                                      let uu____5143 = refine_intro ()  in
                                      bind uu____5143
                                        (fun uu____5147  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5134  in
                             bind uu____5127
                               (fun uu___1_5154  ->
                                  match uu___1_5154 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5163  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5166  -> ret ())
                                  | FStar_Util.Inl uu____5167 ->
                                      mlog
                                        (fun uu____5169  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5172  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5083
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5224 = f x  in
          bind uu____5224
            (fun y  ->
               let uu____5232 = mapM f xs  in
               bind uu____5232 (fun ys  -> ret (y :: ys)))
  
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
            let uu____5342 = f e ty2 ty1  in
            bind uu____5342
              (fun uu___3_5356  ->
                 if uu___3_5356
                 then ret acc
                 else
                   (let uu____5376 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5376 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5397 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5399 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5397
                          uu____5399
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5416 =
                          let uu____5418 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5418  in
                        if uu____5416
                        then fail "Codomain is effectful"
                        else
                          (let uu____5442 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5442
                             (fun uu____5469  ->
                                match uu____5469 with
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
        let uu____5575 =
          mlog
            (fun uu____5580  ->
               let uu____5581 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5581)
            (fun uu____5586  ->
               let uu____5587 = cur_goal ()  in
               bind uu____5587
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5595 = __tc e tm  in
                    bind uu____5595
                      (fun uu____5616  ->
                         match uu____5616 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5629 =
                               let uu____5640 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5640
                                in
                             bind uu____5629
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5661  ->
                                       let uu____5662 =
                                         FStar_Common.string_of_list
                                           (fun uu____5674  ->
                                              match uu____5674 with
                                              | (t,uu____5683,uu____5684) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____5662)
                                    (fun uu____5692  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____5707) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5711 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5734  ->
                                              fun w  ->
                                                match uu____5734 with
                                                | (uvt,q,uu____5752) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____5784 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5801  ->
                                              fun s  ->
                                                match uu____5801 with
                                                | (uu____5813,uu____5814,uv)
                                                    ->
                                                    let uu____5816 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____5816) uvs
                                           uu____5784
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5826 = solve' goal w  in
                                       bind uu____5826
                                         (fun uu____5831  ->
                                            let uu____5832 =
                                              mapM
                                                (fun uu____5849  ->
                                                   match uu____5849 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5861 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5861 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5866 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5867 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____5867
                                                            then ret ()
                                                            else
                                                              (let uu____5874
                                                                 =
                                                                 let uu____5877
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___891_5880
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___891_5880.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___891_5880.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___891_5880.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5877]
                                                                  in
                                                               add_goals
                                                                 uu____5874)))
                                                uvs
                                               in
                                            bind uu____5832
                                              (fun uu____5885  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5575
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5913 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5913
    then
      let uu____5922 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5937 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5990 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5922 with
      | (pre,post) ->
          let post1 =
            let uu____6023 =
              let uu____6034 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6034]  in
            FStar_Syntax_Util.mk_app post uu____6023  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6065 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6065
       then
         let uu____6074 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6074
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
            let uu____6153 = f x e  in
            bind uu____6153 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6168 =
      let uu____6171 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6178  ->
                  let uu____6179 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6179)
               (fun uu____6185  ->
                  let is_unit_t t =
                    let uu____6193 =
                      let uu____6194 = FStar_Syntax_Subst.compress t  in
                      uu____6194.FStar_Syntax_Syntax.n  in
                    match uu____6193 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6200 -> false  in
                  let uu____6202 = cur_goal ()  in
                  bind uu____6202
                    (fun goal  ->
                       let uu____6208 =
                         let uu____6217 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6217 tm  in
                       bind uu____6208
                         (fun uu____6232  ->
                            match uu____6232 with
                            | (tm1,t,guard) ->
                                let uu____6244 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6244 with
                                 | (bs,comp) ->
                                     let uu____6277 = lemma_or_sq comp  in
                                     (match uu____6277 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6297 =
                                            fold_left
                                              (fun uu____6359  ->
                                                 fun uu____6360  ->
                                                   match (uu____6359,
                                                           uu____6360)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6511 =
                                                         is_unit_t b_t  in
                                                       if uu____6511
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
                                                         (let uu____6634 =
                                                            let uu____6641 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6641 b_t
                                                             in
                                                          bind uu____6634
                                                            (fun uu____6672 
                                                               ->
                                                               match uu____6672
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
                                          bind uu____6297
                                            (fun uu____6858  ->
                                               match uu____6858 with
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
                                                   let uu____6946 =
                                                     let uu____6950 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6951 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6952 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6950
                                                       uu____6951 uu____6952
                                                      in
                                                   bind uu____6946
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6963 =
                                                            let uu____6965 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6965
                                                              tm1
                                                             in
                                                          let uu____6966 =
                                                            let uu____6968 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6969 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____6968
                                                              uu____6969
                                                             in
                                                          let uu____6970 =
                                                            let uu____6972 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6973 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6972
                                                              uu____6973
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6963
                                                            uu____6966
                                                            uu____6970
                                                        else
                                                          (let uu____6977 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6977
                                                             (fun uu____6985 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____7011
                                                                    =
                                                                    let uu____7014
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____7014
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____7011
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
                                                                    let uu____7050
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____7050)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____7067
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7067
                                                                  with
                                                                  | (hd1,uu____7086)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____7113)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7130
                                                                    -> false)
                                                                   in
                                                                let uu____7132
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
                                                                    let uu____7175
                                                                    = imp  in
                                                                    match uu____7175
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7186
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7186
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7208)
                                                                    ->
                                                                    let uu____7233
                                                                    =
                                                                    let uu____7234
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7234.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7233
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7242)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1006_7262
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1006_7262.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1006_7262.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1006_7262.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1006_7262.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7265
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7271
                                                                     ->
                                                                    let uu____7272
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7274
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7272
                                                                    uu____7274)
                                                                    (fun
                                                                    uu____7281
                                                                     ->
                                                                    let env =
                                                                    let uu___1011_7283
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1011_7283.FStar_TypeChecker_Env.strict_args_tab)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7286
                                                                    =
                                                                    let uu____7289
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7293
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7295
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7293
                                                                    uu____7295
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7301
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7289
                                                                    uu____7301
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7286
                                                                    (fun
                                                                    uu____7305
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____7132
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
                                                                    let uu____7369
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7369
                                                                    then
                                                                    let uu____7374
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7374
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
                                                                    let uu____7389
                                                                    =
                                                                    let uu____7391
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7391
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7389)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7392
                                                                    =
                                                                    let uu____7395
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7395
                                                                    guard  in
                                                                    bind
                                                                    uu____7392
                                                                    (fun
                                                                    uu____7399
                                                                     ->
                                                                    let uu____7400
                                                                    =
                                                                    let uu____7403
                                                                    =
                                                                    let uu____7405
                                                                    =
                                                                    let uu____7407
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7408
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7407
                                                                    uu____7408
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7405
                                                                     in
                                                                    if
                                                                    uu____7403
                                                                    then
                                                                    let uu____7412
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7412
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7400
                                                                    (fun
                                                                    uu____7417
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6171  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6168
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7441 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7441 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7451::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7511::uu____7512::(e1,uu____7514)::(e2,uu____7516)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7593 ->
        let uu____7596 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7596 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7610 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7610 with
              | (hd1,args) ->
                  let uu____7659 =
                    let uu____7674 =
                      let uu____7675 = FStar_Syntax_Subst.compress hd1  in
                      uu____7675.FStar_Syntax_Syntax.n  in
                    (uu____7674, args)  in
                  (match uu____7659 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7695,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7696))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____7764 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7801 = destruct_eq' typ  in
    match uu____7801 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7831 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7831 with
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
        let uu____7900 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7900 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7958 = aux e'  in
               FStar_Util.map_opt uu____7958
                 (fun uu____7989  ->
                    match uu____7989 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8015 = aux e  in
      FStar_Util.map_opt uu____8015
        (fun uu____8046  ->
           match uu____8046 with
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
          let uu____8120 =
            let uu____8131 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8131  in
          FStar_Util.map_opt uu____8120
            (fun uu____8149  ->
               match uu____8149 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1119_8171 = bv  in
                     let uu____8172 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1119_8171.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1119_8171.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____8172
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1123_8180 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____8181 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____8190 =
                       let uu____8193 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____8193  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1123_8180.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____8181;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____8190;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1123_8180.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1123_8180.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1123_8180.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1123_8180.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1126_8194 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1126_8194.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1126_8194.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1126_8194.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1126_8194.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8205 =
      let uu____8208 = cur_goal ()  in
      bind uu____8208
        (fun goal  ->
           let uu____8216 = h  in
           match uu____8216 with
           | (bv,uu____8220) ->
               mlog
                 (fun uu____8228  ->
                    let uu____8229 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8231 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8229
                      uu____8231)
                 (fun uu____8236  ->
                    let uu____8237 =
                      let uu____8248 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8248  in
                    match uu____8237 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8275 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8275 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8290 =
                               let uu____8291 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8291.FStar_Syntax_Syntax.n  in
                             (match uu____8290 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1149_8308 = bv2  in
                                    let uu____8309 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1149_8308.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1149_8308.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8309
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1153_8317 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8318 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8327 =
                                      let uu____8330 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8330
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1153_8317.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8318;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8327;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1153_8317.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1153_8317.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1153_8317.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1153_8317.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1156_8333 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1156_8333.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1156_8333.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1156_8333.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1156_8333.FStar_Tactics_Types.label)
                                     })
                              | uu____8334 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8336 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8205
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____8366 =
        let uu____8369 = cur_goal ()  in
        bind uu____8369
          (fun goal  ->
             let uu____8380 = b  in
             match uu____8380 with
             | (bv,uu____8384) ->
                 let bv' =
                   let uu____8390 =
                     let uu___1167_8391 = bv  in
                     let uu____8392 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8392;
                       FStar_Syntax_Syntax.index =
                         (uu___1167_8391.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1167_8391.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8390  in
                 let s1 =
                   let uu____8397 =
                     let uu____8398 =
                       let uu____8405 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8405)  in
                     FStar_Syntax_Syntax.NT uu____8398  in
                   [uu____8397]  in
                 let uu____8410 = subst_goal bv bv' s1 goal  in
                 (match uu____8410 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8366
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8432 =
      let uu____8435 = cur_goal ()  in
      bind uu____8435
        (fun goal  ->
           let uu____8444 = b  in
           match uu____8444 with
           | (bv,uu____8448) ->
               let uu____8453 =
                 let uu____8464 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8464  in
               (match uu____8453 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8491 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8491 with
                     | (ty,u) ->
                         let uu____8500 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8500
                           (fun uu____8519  ->
                              match uu____8519 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1191_8529 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1191_8529.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1191_8529.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8533 =
                                      let uu____8534 =
                                        let uu____8541 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8541)  in
                                      FStar_Syntax_Syntax.NT uu____8534  in
                                    [uu____8533]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1196_8553 = b1  in
                                         let uu____8554 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1196_8553.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1196_8553.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8554
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8561  ->
                                       let new_goal =
                                         let uu____8563 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8564 =
                                           let uu____8565 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8565
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8563 uu____8564
                                          in
                                       let uu____8566 = add_goals [new_goal]
                                          in
                                       bind uu____8566
                                         (fun uu____8571  ->
                                            let uu____8572 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8572
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8432
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8598 =
        let uu____8601 = cur_goal ()  in
        bind uu____8601
          (fun goal  ->
             let uu____8610 = b  in
             match uu____8610 with
             | (bv,uu____8614) ->
                 let uu____8619 =
                   let uu____8630 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8630  in
                 (match uu____8619 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8660 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8660
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1217_8665 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1217_8665.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1217_8665.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8667 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8667))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8598
  
let (revert : unit -> unit tac) =
  fun uu____8680  ->
    let uu____8683 = cur_goal ()  in
    bind uu____8683
      (fun goal  ->
         let uu____8689 =
           let uu____8696 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8696  in
         match uu____8689 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8713 =
                 let uu____8716 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8716  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8713
                in
             let uu____8731 = new_uvar "revert" env' typ'  in
             bind uu____8731
               (fun uu____8747  ->
                  match uu____8747 with
                  | (r,u_r) ->
                      let uu____8756 =
                        let uu____8759 =
                          let uu____8760 =
                            let uu____8761 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8761.FStar_Syntax_Syntax.pos  in
                          let uu____8764 =
                            let uu____8769 =
                              let uu____8770 =
                                let uu____8779 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8779  in
                              [uu____8770]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8769  in
                          uu____8764 FStar_Pervasives_Native.None uu____8760
                           in
                        set_solution goal uu____8759  in
                      bind uu____8756
                        (fun uu____8798  ->
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
      let uu____8812 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8812
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8828 = cur_goal ()  in
    bind uu____8828
      (fun goal  ->
         mlog
           (fun uu____8836  ->
              let uu____8837 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8839 =
                let uu____8841 =
                  let uu____8843 =
                    let uu____8852 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8852  in
                  FStar_All.pipe_right uu____8843 FStar_List.length  in
                FStar_All.pipe_right uu____8841 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8837 uu____8839)
           (fun uu____8873  ->
              let uu____8874 =
                let uu____8885 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8885  in
              match uu____8874 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8930 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8930
                        then
                          let uu____8935 =
                            let uu____8937 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8937
                             in
                          fail uu____8935
                        else check1 bvs2
                     in
                  let uu____8942 =
                    let uu____8944 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8944  in
                  if uu____8942
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8951 = check1 bvs  in
                     bind uu____8951
                       (fun uu____8957  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8959 =
                            let uu____8966 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8966  in
                          bind uu____8959
                            (fun uu____8976  ->
                               match uu____8976 with
                               | (ut,uvar_ut) ->
                                   let uu____8985 = set_solution goal ut  in
                                   bind uu____8985
                                     (fun uu____8990  ->
                                        let uu____8991 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8991))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8999  ->
    let uu____9002 = cur_goal ()  in
    bind uu____9002
      (fun goal  ->
         let uu____9008 =
           let uu____9015 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9015  in
         match uu____9008 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9024) ->
             let uu____9029 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9029)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9042 = cur_goal ()  in
    bind uu____9042
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9052 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9052  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9055  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9068 = cur_goal ()  in
    bind uu____9068
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9078 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9078  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9081  -> add_goals [g']))
  
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
            let uu____9122 = FStar_Syntax_Subst.compress t  in
            uu____9122.FStar_Syntax_Syntax.n  in
          let uu____9125 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1401_9132 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1401_9132.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1401_9132.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9125
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9149 =
                   let uu____9150 = FStar_Syntax_Subst.compress t1  in
                   uu____9150.FStar_Syntax_Syntax.n  in
                 match uu____9149 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9181 = ff hd1  in
                     bind uu____9181
                       (fun hd2  ->
                          let fa uu____9207 =
                            match uu____9207 with
                            | (a,q) ->
                                let uu____9228 = ff a  in
                                bind uu____9228 (fun a1  -> ret (a1, q))
                             in
                          let uu____9247 = mapM fa args  in
                          bind uu____9247
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9329 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9329 with
                      | (bs1,t') ->
                          let uu____9338 =
                            let uu____9341 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9341 t'  in
                          bind uu____9338
                            (fun t''  ->
                               let uu____9345 =
                                 let uu____9346 =
                                   let uu____9365 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9374 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9365, uu____9374, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9346  in
                               ret uu____9345))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9449 = ff hd1  in
                     bind uu____9449
                       (fun hd2  ->
                          let ffb br =
                            let uu____9464 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9464 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9496 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9496  in
                                let uu____9497 = ff1 e  in
                                bind uu____9497
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9512 = mapM ffb brs  in
                          bind uu____9512
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9556;
                          FStar_Syntax_Syntax.lbtyp = uu____9557;
                          FStar_Syntax_Syntax.lbeff = uu____9558;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9560;
                          FStar_Syntax_Syntax.lbpos = uu____9561;_}::[]),e)
                     ->
                     let lb =
                       let uu____9589 =
                         let uu____9590 = FStar_Syntax_Subst.compress t1  in
                         uu____9590.FStar_Syntax_Syntax.n  in
                       match uu____9589 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9594) -> lb
                       | uu____9610 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9620 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9620
                         (fun def1  ->
                            ret
                              (let uu___1354_9626 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1354_9626.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1354_9626.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1354_9626.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1354_9626.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1354_9626.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1354_9626.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9627 = fflb lb  in
                     bind uu____9627
                       (fun lb1  ->
                          let uu____9637 =
                            let uu____9642 =
                              let uu____9643 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9643]  in
                            FStar_Syntax_Subst.open_term uu____9642 e  in
                          match uu____9637 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9673 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9673  in
                              let uu____9674 = ff1 e1  in
                              bind uu____9674
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9721 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9721
                         (fun def  ->
                            ret
                              (let uu___1372_9727 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1372_9727.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1372_9727.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1372_9727.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1372_9727.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1372_9727.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1372_9727.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9728 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9728 with
                      | (lbs1,e1) ->
                          let uu____9743 = mapM fflb lbs1  in
                          bind uu____9743
                            (fun lbs2  ->
                               let uu____9755 = ff e1  in
                               bind uu____9755
                                 (fun e2  ->
                                    let uu____9763 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9763 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9834 = ff t2  in
                     bind uu____9834
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9865 = ff t2  in
                     bind uu____9865
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9872 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1396_9879 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1396_9879.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1396_9879.FStar_Syntax_Syntax.vars)
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
              let uu____9926 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1409_9935 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1409_9935.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1409_9935.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1409_9935.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1409_9935.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1409_9935.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1409_9935.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1409_9935.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1409_9935.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1409_9935.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1409_9935.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1409_9935.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1409_9935.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1409_9935.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1409_9935.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1409_9935.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1409_9935.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1409_9935.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1409_9935.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1409_9935.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1409_9935.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1409_9935.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1409_9935.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1409_9935.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1409_9935.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1409_9935.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1409_9935.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1409_9935.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1409_9935.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1409_9935.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1409_9935.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1409_9935.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1409_9935.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1409_9935.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1409_9935.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1409_9935.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1409_9935.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1409_9935.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1409_9935.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1409_9935.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1409_9935.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1409_9935.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___1409_9935.FStar_TypeChecker_Env.strict_args_tab)
                   }) t
                 in
              match uu____9926 with
              | (t1,lcomp,g) ->
                  let uu____9942 =
                    (let uu____9946 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9946) ||
                      (let uu____9949 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9949)
                     in
                  if uu____9942
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9960 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9960
                         (fun uu____9977  ->
                            match uu____9977 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9990  ->
                                      let uu____9991 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9993 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9991 uu____9993);
                                 (let uu____9996 =
                                    let uu____9999 =
                                      let uu____10000 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10000
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9999
                                      opts label1
                                     in
                                  bind uu____9996
                                    (fun uu____10004  ->
                                       let uu____10005 =
                                         bind tau
                                           (fun uu____10011  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____10017  ->
                                                   let uu____10018 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____10020 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____10018 uu____10020);
                                              ret ut1)
                                          in
                                       focus uu____10005))))
                        in
                     let uu____10023 = catch rewrite_eq  in
                     bind uu____10023
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
          let uu____10235 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10235
            (fun t1  ->
               let uu____10243 =
                 f env
                   (let uu___1486_10251 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1486_10251.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1486_10251.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10243
                 (fun uu____10267  ->
                    match uu____10267 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10290 =
                               let uu____10291 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10291.FStar_Syntax_Syntax.n  in
                             match uu____10290 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10328 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10328
                                   (fun uu____10350  ->
                                      match uu____10350 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10366 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10366
                                            (fun uu____10390  ->
                                               match uu____10390 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1466_10420 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1466_10420.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1466_10420.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10462 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10462 with
                                  | (bs1,t') ->
                                      let uu____10477 =
                                        let uu____10484 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10484 ctrl1 t'
                                         in
                                      bind uu____10477
                                        (fun uu____10499  ->
                                           match uu____10499 with
                                           | (t'',ctrl2) ->
                                               let uu____10514 =
                                                 let uu____10521 =
                                                   let uu___1479_10524 = t4
                                                      in
                                                   let uu____10527 =
                                                     let uu____10528 =
                                                       let uu____10547 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10556 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10547,
                                                         uu____10556, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10528
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10527;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1479_10524.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1479_10524.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10521, ctrl2)  in
                                               ret uu____10514))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10609 -> ret (t3, ctrl1))))

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
              let uu____10655 = ctrl_tac_fold f env ctrl t  in
              bind uu____10655
                (fun uu____10676  ->
                   match uu____10676 with
                   | (t1,ctrl1) ->
                       let uu____10691 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10691
                         (fun uu____10715  ->
                            match uu____10715 with
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
                let uu____10806 =
                  let uu____10814 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10814
                    (fun uu____10825  ->
                       let uu____10826 = ctrl t1  in
                       bind uu____10826
                         (fun res  ->
                            let uu____10852 = trivial ()  in
                            bind uu____10852 (fun uu____10861  -> ret res)))
                   in
                bind uu____10806
                  (fun uu____10879  ->
                     match uu____10879 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10908 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1516_10917 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1516_10917.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1516_10917.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1516_10917.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1516_10917.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1516_10917.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1516_10917.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1516_10917.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1516_10917.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1516_10917.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1516_10917.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1516_10917.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1516_10917.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1516_10917.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1516_10917.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1516_10917.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1516_10917.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1516_10917.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1516_10917.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1516_10917.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1516_10917.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1516_10917.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1516_10917.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1516_10917.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1516_10917.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1516_10917.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1516_10917.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1516_10917.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1516_10917.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1516_10917.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1516_10917.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1516_10917.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1516_10917.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1516_10917.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1516_10917.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1516_10917.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1516_10917.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1516_10917.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1516_10917.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1516_10917.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1516_10917.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1516_10917.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___1516_10917.FStar_TypeChecker_Env.strict_args_tab)
                                 }) t1
                               in
                            match uu____10908 with
                            | (t2,lcomp,g) ->
                                let uu____10928 =
                                  (let uu____10932 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10932) ||
                                    (let uu____10935 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10935)
                                   in
                                if uu____10928
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10951 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10951
                                     (fun uu____10972  ->
                                        match uu____10972 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10989  ->
                                                  let uu____10990 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10992 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10990 uu____10992);
                                             (let uu____10995 =
                                                let uu____10998 =
                                                  let uu____10999 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10999 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10998 opts label1
                                                 in
                                              bind uu____10995
                                                (fun uu____11007  ->
                                                   let uu____11008 =
                                                     bind rewriter
                                                       (fun uu____11022  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____11028 
                                                               ->
                                                               let uu____11029
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____11031
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____11029
                                                                 uu____11031);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11008)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____11076 =
        bind get
          (fun ps  ->
             let uu____11086 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11086 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11124  ->
                       let uu____11125 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11125);
                  bind dismiss_all
                    (fun uu____11130  ->
                       let uu____11131 =
                         let uu____11138 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11138
                           keepGoing gt1
                          in
                       bind uu____11131
                         (fun uu____11148  ->
                            match uu____11148 with
                            | (gt',uu____11156) ->
                                (log ps
                                   (fun uu____11160  ->
                                      let uu____11161 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____11161);
                                 (let uu____11164 = push_goals gs  in
                                  bind uu____11164
                                    (fun uu____11169  ->
                                       let uu____11170 =
                                         let uu____11173 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____11173]  in
                                       add_goals uu____11170)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11076
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11198 =
        bind get
          (fun ps  ->
             let uu____11208 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11208 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11246  ->
                       let uu____11247 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11247);
                  bind dismiss_all
                    (fun uu____11252  ->
                       let uu____11253 =
                         let uu____11256 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11256 gt1
                          in
                       bind uu____11253
                         (fun gt'  ->
                            log ps
                              (fun uu____11264  ->
                                 let uu____11265 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11265);
                            (let uu____11268 = push_goals gs  in
                             bind uu____11268
                               (fun uu____11273  ->
                                  let uu____11274 =
                                    let uu____11277 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11277]  in
                                  add_goals uu____11274))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____11198
  
let (_trefl :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit tac) =
  fun l  ->
    fun r  ->
      let uu____11298 = cur_goal ()  in
      bind uu____11298
        (fun g  ->
           let uu____11304 =
             let uu____11308 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11308 l r  in
           bind uu____11304
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____11319 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11319 l
                      in
                   let r1 =
                     let uu____11321 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11321 r
                      in
                   let uu____11322 =
                     let uu____11326 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11326 l1 r1  in
                   bind uu____11322
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____11336 =
                             let uu____11338 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11338 l1  in
                           let uu____11339 =
                             let uu____11341 = FStar_Tactics_Types.goal_env g
                                in
                             tts uu____11341 r1  in
                           fail2 "not a trivial equality ((%s) vs (%s))"
                             uu____11336 uu____11339)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11350  ->
    let uu____11353 =
      let uu____11356 = cur_goal ()  in
      bind uu____11356
        (fun g  ->
           let uu____11364 =
             let uu____11371 = FStar_Tactics_Types.goal_type g  in
             destruct_eq uu____11371  in
           match uu____11364 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11384 =
                 let uu____11386 = FStar_Tactics_Types.goal_env g  in
                 let uu____11387 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11386 uu____11387  in
               fail1 "not an equality (%s)" uu____11384)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11353
  
let (dup : unit -> unit tac) =
  fun uu____11401  ->
    let uu____11404 = cur_goal ()  in
    bind uu____11404
      (fun g  ->
         let uu____11410 =
           let uu____11417 = FStar_Tactics_Types.goal_env g  in
           let uu____11418 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11417 uu____11418  in
         bind uu____11410
           (fun uu____11428  ->
              match uu____11428 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1596_11438 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1596_11438.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1596_11438.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1596_11438.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1596_11438.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11441  ->
                       let uu____11442 =
                         let uu____11445 = FStar_Tactics_Types.goal_env g  in
                         let uu____11446 =
                           let uu____11447 =
                             let uu____11448 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11449 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11448
                               uu____11449
                              in
                           let uu____11450 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11451 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11447 uu____11450 u
                             uu____11451
                            in
                         add_irrelevant_goal "dup equation" uu____11445
                           uu____11446 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11442
                         (fun uu____11455  ->
                            let uu____11456 = add_goals [g']  in
                            bind uu____11456 (fun uu____11460  -> ret ())))))
  
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
              let uu____11586 = f x y  in
              if uu____11586 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11609 -> (acc, l11, l21)  in
        let uu____11624 = aux [] l1 l2  in
        match uu____11624 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11730 = get_phi g1  in
      match uu____11730 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11737 = get_phi g2  in
          (match uu____11737 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11750 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11750 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11781 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11781 phi1  in
                    let t2 =
                      let uu____11791 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11791 phi2  in
                    let uu____11800 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11800
                      (fun uu____11805  ->
                         let uu____11806 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11806
                           (fun uu____11813  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1647_11818 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11819 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1647_11818.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1647_11818.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1647_11818.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1647_11818.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11819;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1647_11818.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1647_11818.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1647_11818.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1647_11818.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1647_11818.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1647_11818.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1647_11818.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1647_11818.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1647_11818.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1647_11818.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1647_11818.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1647_11818.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1647_11818.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1647_11818.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1647_11818.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1647_11818.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1647_11818.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1647_11818.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1647_11818.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1647_11818.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1647_11818.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1647_11818.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1647_11818.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1647_11818.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1647_11818.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1647_11818.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1647_11818.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1647_11818.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1647_11818.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1647_11818.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1647_11818.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1647_11818.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1647_11818.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1647_11818.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1647_11818.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1647_11818.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1647_11818.FStar_TypeChecker_Env.strict_args_tab)
                                }  in
                              let uu____11823 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11823
                                (fun goal  ->
                                   mlog
                                     (fun uu____11833  ->
                                        let uu____11834 =
                                          goal_to_string_verbose g1  in
                                        let uu____11836 =
                                          goal_to_string_verbose g2  in
                                        let uu____11838 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11834 uu____11836 uu____11838)
                                     (fun uu____11842  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11850  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11866 =
               set
                 (let uu___1662_11871 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1662_11871.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1662_11871.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1662_11871.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1662_11871.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1662_11871.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1662_11871.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1662_11871.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1662_11871.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1662_11871.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1662_11871.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1662_11871.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1662_11871.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11866
               (fun uu____11874  ->
                  let uu____11875 = join_goals g1 g2  in
                  bind uu____11875 (fun g12  -> add_goals [g12]))
         | uu____11880 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11896 =
      let uu____11899 = cur_goal ()  in
      bind uu____11899
        (fun g  ->
           FStar_Options.push ();
           (let uu____11912 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11912);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1673_11919 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1673_11919.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1673_11919.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1673_11919.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1673_11919.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11896
  
let (top_env : unit -> env tac) =
  fun uu____11936  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11951  ->
    let uu____11955 = cur_goal ()  in
    bind uu____11955
      (fun g  ->
         let uu____11962 =
           (FStar_Options.lax ()) ||
             (let uu____11965 = FStar_Tactics_Types.goal_env g  in
              uu____11965.FStar_TypeChecker_Env.lax)
            in
         ret uu____11962)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11982 =
        mlog
          (fun uu____11987  ->
             let uu____11988 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11988)
          (fun uu____11993  ->
             let uu____11994 = cur_goal ()  in
             bind uu____11994
               (fun goal  ->
                  let env =
                    let uu____12002 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12002 ty  in
                  let uu____12003 = __tc_ghost env tm  in
                  bind uu____12003
                    (fun uu____12022  ->
                       match uu____12022 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12036  ->
                                let uu____12037 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12037)
                             (fun uu____12041  ->
                                mlog
                                  (fun uu____12044  ->
                                     let uu____12045 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12045)
                                  (fun uu____12050  ->
                                     let uu____12051 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12051
                                       (fun uu____12056  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11982
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12081 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12087 =
              let uu____12094 =
                let uu____12095 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12095
                 in
              new_uvar "uvar_env.2" env uu____12094  in
            bind uu____12087
              (fun uu____12112  ->
                 match uu____12112 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12081
        (fun typ  ->
           let uu____12124 = new_uvar "uvar_env" env typ  in
           bind uu____12124
             (fun uu____12139  ->
                match uu____12139 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12158 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12177 -> g.FStar_Tactics_Types.opts
             | uu____12180 -> FStar_Options.peek ()  in
           let uu____12183 = FStar_Syntax_Util.head_and_args t  in
           match uu____12183 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12203);
                FStar_Syntax_Syntax.pos = uu____12204;
                FStar_Syntax_Syntax.vars = uu____12205;_},uu____12206)
               ->
               let env1 =
                 let uu___1727_12248 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1727_12248.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1727_12248.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1727_12248.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1727_12248.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1727_12248.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1727_12248.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1727_12248.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1727_12248.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1727_12248.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1727_12248.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1727_12248.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1727_12248.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1727_12248.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1727_12248.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1727_12248.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1727_12248.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1727_12248.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1727_12248.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1727_12248.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1727_12248.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1727_12248.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1727_12248.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1727_12248.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1727_12248.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1727_12248.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1727_12248.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1727_12248.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1727_12248.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1727_12248.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1727_12248.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1727_12248.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1727_12248.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1727_12248.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1727_12248.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1727_12248.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1727_12248.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1727_12248.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1727_12248.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1727_12248.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1727_12248.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1727_12248.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1727_12248.FStar_TypeChecker_Env.strict_args_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12252 =
                 let uu____12255 = bnorm_goal g  in [uu____12255]  in
               add_goals uu____12252
           | uu____12256 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12158
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12318 = if b then t2 else ret false  in
             bind uu____12318 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12344 = trytac comp  in
      bind uu____12344
        (fun uu___4_12356  ->
           match uu___4_12356 with
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
        let uu____12398 =
          bind get
            (fun ps  ->
               let uu____12406 = __tc e t1  in
               bind uu____12406
                 (fun uu____12427  ->
                    match uu____12427 with
                    | (t11,ty1,g1) ->
                        let uu____12440 = __tc e t2  in
                        bind uu____12440
                          (fun uu____12461  ->
                             match uu____12461 with
                             | (t21,ty2,g2) ->
                                 let uu____12474 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12474
                                   (fun uu____12481  ->
                                      let uu____12482 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12482
                                        (fun uu____12490  ->
                                           let uu____12491 =
                                             do_unify e ty1 ty2  in
                                           let uu____12495 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12491 uu____12495)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12398
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12543  ->
             let uu____12544 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12544
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
        (fun uu____12578  ->
           let uu____12579 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12579)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12590 =
      mlog
        (fun uu____12595  ->
           let uu____12596 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12596)
        (fun uu____12601  ->
           let uu____12602 = cur_goal ()  in
           bind uu____12602
             (fun g  ->
                let uu____12608 =
                  let uu____12617 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12617 ty  in
                bind uu____12608
                  (fun uu____12629  ->
                     match uu____12629 with
                     | (ty1,uu____12639,guard) ->
                         let uu____12641 =
                           let uu____12644 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12644 guard  in
                         bind uu____12641
                           (fun uu____12648  ->
                              let uu____12649 =
                                let uu____12653 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12654 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12653 uu____12654 ty1  in
                              bind uu____12649
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12663 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12663
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12670 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12671 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12670
                                          uu____12671
                                         in
                                      let nty =
                                        let uu____12673 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12673 ty1  in
                                      let uu____12674 =
                                        let uu____12678 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12678 ng nty  in
                                      bind uu____12674
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12687 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12687
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12590
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12761 =
      let uu____12770 = cur_goal ()  in
      bind uu____12770
        (fun g  ->
           let uu____12782 =
             let uu____12791 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12791 s_tm  in
           bind uu____12782
             (fun uu____12809  ->
                match uu____12809 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12827 =
                      let uu____12830 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12830 guard  in
                    bind uu____12827
                      (fun uu____12843  ->
                         let uu____12844 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12844 with
                         | (h,args) ->
                             let uu____12889 =
                               let uu____12896 =
                                 let uu____12897 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12897.FStar_Syntax_Syntax.n  in
                               match uu____12896 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12912;
                                      FStar_Syntax_Syntax.vars = uu____12913;_},us)
                                   -> ret (fv, us)
                               | uu____12923 -> fail "type is not an fv"  in
                             bind uu____12889
                               (fun uu____12944  ->
                                  match uu____12944 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12960 =
                                        let uu____12963 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12963 t_lid
                                         in
                                      (match uu____12960 with
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
                                                  (fun uu____13014  ->
                                                     let uu____13015 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____13015 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____13030 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____13058
                                                                  =
                                                                  let uu____13061
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13061
                                                                    c_lid
                                                                   in
                                                                match uu____13058
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
                                                                    uu____13135
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
                                                                    let uu____13140
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13140
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13163
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13163
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13206
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____13206
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____13279
                                                                    =
                                                                    let uu____13281
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____13281
                                                                     in
                                                                    failwhen
                                                                    uu____13279
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13300
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
                                                                    uu___5_13317
                                                                    =
                                                                    match uu___5_13317
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13321)
                                                                    -> true
                                                                    | 
                                                                    uu____13324
                                                                    -> false
                                                                     in
                                                                    let uu____13328
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13328
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
                                                                    uu____13462
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
                                                                    uu____13524
                                                                     ->
                                                                    match uu____13524
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13544),
                                                                    (t,uu____13546))
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
                                                                    uu____13616
                                                                     ->
                                                                    match uu____13616
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13643),
                                                                    (t,uu____13645))
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
                                                                    uu____13704
                                                                     ->
                                                                    match uu____13704
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
                                                                    let uu____13759
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1891_13776
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1891_13776.FStar_TypeChecker_Env.strict_args_tab)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13759
                                                                    with
                                                                    | 
                                                                    (uu____13790,uu____13791,uu____13792,pat_t,uu____13794,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13801
                                                                    =
                                                                    let uu____13802
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13802
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13801
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13807
                                                                    =
                                                                    let uu____13816
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13816]
                                                                     in
                                                                    let uu____13835
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13807
                                                                    uu____13835
                                                                     in
                                                                    let nty =
                                                                    let uu____13841
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13841
                                                                     in
                                                                    let uu____13844
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13844
                                                                    (fun
                                                                    uu____13874
                                                                     ->
                                                                    match uu____13874
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
                                                                    let uu____13901
                                                                    =
                                                                    let uu____13912
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13912]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13901
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13948
                                                                    =
                                                                    let uu____13959
                                                                    =
                                                                    let uu____13964
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13964)
                                                                     in
                                                                    (g', br,
                                                                    uu____13959)
                                                                     in
                                                                    ret
                                                                    uu____13948))))))
                                                                    | 
                                                                    uu____13985
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____13030
                                                           (fun goal_brs  ->
                                                              let uu____14035
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____14035
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
                                                                  let uu____14108
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____14108
                                                                    (
                                                                    fun
                                                                    uu____14119
                                                                     ->
                                                                    let uu____14120
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14120
                                                                    (fun
                                                                    uu____14130
                                                                     ->
                                                                    ret infos))))
                                            | uu____14137 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12761
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14186::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14216 = init xs  in x :: uu____14216
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14229 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14238) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14304 = last args  in
          (match uu____14304 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14334 =
                 let uu____14335 =
                   let uu____14340 =
                     let uu____14341 =
                       let uu____14346 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14346  in
                     uu____14341 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14340, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14335  in
               FStar_All.pipe_left ret uu____14334)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14357,uu____14358) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14411 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14411 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14453 =
                      let uu____14454 =
                        let uu____14459 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14459)  in
                      FStar_Reflection_Data.Tv_Abs uu____14454  in
                    FStar_All.pipe_left ret uu____14453))
      | FStar_Syntax_Syntax.Tm_type uu____14462 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14487 ->
          let uu____14502 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14502 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14533 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14533 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14586 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14599 =
            let uu____14600 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14600  in
          FStar_All.pipe_left ret uu____14599
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14621 =
            let uu____14622 =
              let uu____14627 =
                let uu____14628 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14628  in
              (uu____14627, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14622  in
          FStar_All.pipe_left ret uu____14621
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14668 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14673 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14673 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14726 ->
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
             | FStar_Util.Inr uu____14768 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14772 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14772 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14792 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14798 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14853 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14853
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14874 =
                  let uu____14881 =
                    FStar_List.map
                      (fun uu____14894  ->
                         match uu____14894 with
                         | (p1,uu____14903) -> inspect_pat p1) ps
                     in
                  (fv, uu____14881)  in
                FStar_Reflection_Data.Pat_Cons uu____14874
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
              (fun uu___6_14999  ->
                 match uu___6_14999 with
                 | (pat,uu____15021,t5) ->
                     let uu____15039 = inspect_pat pat  in (uu____15039, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____15048 ->
          ((let uu____15050 =
              let uu____15056 =
                let uu____15058 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15060 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15058 uu____15060
                 in
              (FStar_Errors.Warning_CantInspect, uu____15056)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15050);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14229
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15078 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15078
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15082 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15082
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15086 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15086
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15093 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15093
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15118 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15118
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15135 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15135
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15154 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15154
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15158 =
          let uu____15159 =
            let uu____15166 =
              let uu____15167 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15167  in
            FStar_Syntax_Syntax.mk uu____15166  in
          uu____15159 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15158
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15172 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15172
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15183 =
          let uu____15184 =
            let uu____15191 =
              let uu____15192 =
                let uu____15206 =
                  let uu____15209 =
                    let uu____15210 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15210]  in
                  FStar_Syntax_Subst.close uu____15209 t2  in
                ((false, [lb]), uu____15206)  in
              FStar_Syntax_Syntax.Tm_let uu____15192  in
            FStar_Syntax_Syntax.mk uu____15191  in
          uu____15184 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15183
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15252 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15252 with
         | (lbs,body) ->
             let uu____15267 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15267)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15304 =
                let uu____15305 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15305  in
              FStar_All.pipe_left wrap uu____15304
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15312 =
                let uu____15313 =
                  let uu____15327 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15345 = pack_pat p1  in
                         (uu____15345, false)) ps
                     in
                  (fv, uu____15327)  in
                FStar_Syntax_Syntax.Pat_cons uu____15313  in
              FStar_All.pipe_left wrap uu____15312
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
            (fun uu___7_15394  ->
               match uu___7_15394 with
               | (pat,t1) ->
                   let uu____15411 = pack_pat pat  in
                   (uu____15411, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15459 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15459
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15487 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15487
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15533 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15533
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15572 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15572
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15592 =
        bind get
          (fun ps  ->
             let uu____15598 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15598 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15592
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15632 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2189_15639 = ps  in
                 let uu____15640 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2189_15639.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2189_15639.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2189_15639.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2189_15639.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2189_15639.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2189_15639.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2189_15639.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2189_15639.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2189_15639.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2189_15639.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2189_15639.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2189_15639.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15640
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15632
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15667 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15667 with
      | (u,ctx_uvars,g_u) ->
          let uu____15700 = FStar_List.hd ctx_uvars  in
          (match uu____15700 with
           | (ctx_uvar,uu____15714) ->
               let g =
                 let uu____15716 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15716 false
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
        let uu____15739 = goal_of_goal_ty env typ  in
        match uu____15739 with
        | (g,g_u) ->
            let ps =
              let uu____15751 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15754 = FStar_Util.psmap_empty ()  in
              {
                FStar_Tactics_Types.main_context = env;
                FStar_Tactics_Types.main_goal = g;
                FStar_Tactics_Types.all_implicits =
                  (g_u.FStar_TypeChecker_Env.implicits);
                FStar_Tactics_Types.goals = [g];
                FStar_Tactics_Types.smt_goals = [];
                FStar_Tactics_Types.depth = Prims.int_zero;
                FStar_Tactics_Types.__dump = do_dump_proofstate;
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = Prims.int_zero;
                FStar_Tactics_Types.tac_verb_dbg = uu____15751;
                FStar_Tactics_Types.local_state = uu____15754
              }  in
            let uu____15759 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15759)
  