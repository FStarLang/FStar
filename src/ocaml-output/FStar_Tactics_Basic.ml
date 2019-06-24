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
          if uu____409 then t1 else aux (i + (Prims.parse_int "1"))  in
        let uu____416 = f b  in
        if uu____416 then b else aux (Prims.parse_int "0")  in
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
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____1060 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
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
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1389  ->
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
         (let uu____1420 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____1420 msg);
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
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
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
                    FStar_Options.set_options FStar_Options.Set
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
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___343_2165 = ps  in
         let uu____2166 =
           FStar_List.filter
             (fun g  ->
                let uu____2172 = check_goal_solved g  in
                FStar_Option.isNone uu____2172) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___343_2165.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___343_2165.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___343_2165.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2166;
           FStar_Tactics_Types.smt_goals =
             (uu___343_2165.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___343_2165.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___343_2165.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___343_2165.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___343_2165.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___343_2165.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___343_2165.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___343_2165.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___343_2165.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2190 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____2190 with
      | FStar_Pervasives_Native.Some uu____2195 ->
          let uu____2196 =
            let uu____2198 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____2198  in
          fail uu____2196
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____2219 = FStar_Tactics_Types.goal_env goal  in
      let uu____2220 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____2219 solution uu____2220
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____2227 =
         let uu___356_2228 = p  in
         let uu____2229 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___356_2228.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___356_2228.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___356_2228.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2229;
           FStar_Tactics_Types.smt_goals =
             (uu___356_2228.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___356_2228.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___356_2228.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___356_2228.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___356_2228.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___356_2228.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___356_2228.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___356_2228.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___356_2228.FStar_Tactics_Types.local_state)
         }  in
       set uu____2227)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____2251  ->
           let uu____2252 =
             let uu____2254 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____2254  in
           let uu____2255 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____2252 uu____2255)
        (fun uu____2260  ->
           let uu____2261 = trysolve goal solution  in
           bind uu____2261
             (fun b  ->
                if b
                then bind __dismiss (fun uu____2273  -> remove_solved_goals)
                else
                  (let uu____2276 =
                     let uu____2278 =
                       let uu____2280 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____2280 solution  in
                     let uu____2281 =
                       let uu____2283 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2284 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____2283 uu____2284  in
                     let uu____2285 =
                       let uu____2287 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2288 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____2287 uu____2288  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____2278 uu____2281 uu____2285
                      in
                   fail uu____2276)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2305 = set_solution goal solution  in
      bind uu____2305
        (fun uu____2309  ->
           bind __dismiss (fun uu____2311  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___372_2330 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_2330.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_2330.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_2330.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___372_2330.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_2330.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_2330.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_2330.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_2330.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_2330.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_2330.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_2330.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_2330.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___376_2349 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___376_2349.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___376_2349.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___376_2349.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___376_2349.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___376_2349.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___376_2349.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___376_2349.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___376_2349.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___376_2349.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___376_2349.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___376_2349.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___376_2349.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2365 = FStar_Options.defensive ()  in
    if uu____2365
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2375 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2375)
         in
      let b2 =
        b1 &&
          (let uu____2379 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2379)
         in
      let rec aux b3 e =
        let uu____2394 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2394 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2414 =
        (let uu____2418 = aux b2 env  in Prims.op_Negation uu____2418) &&
          (let uu____2421 = FStar_ST.op_Bang nwarn  in
           uu____2421 < (Prims.parse_int "5"))
         in
      (if uu____2414
       then
         ((let uu____2447 =
             let uu____2448 = FStar_Tactics_Types.goal_type g  in
             uu____2448.FStar_Syntax_Syntax.pos  in
           let uu____2451 =
             let uu____2457 =
               let uu____2459 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2459
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2457)  in
           FStar_Errors.log_issue uu____2447 uu____2451);
          (let uu____2463 =
             let uu____2465 = FStar_ST.op_Bang nwarn  in
             uu____2465 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____2463))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___398_2534 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___398_2534.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___398_2534.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___398_2534.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___398_2534.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___398_2534.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___398_2534.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___398_2534.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___398_2534.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___398_2534.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___398_2534.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___398_2534.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___398_2534.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___403_2555 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___403_2555.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___403_2555.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___403_2555.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___403_2555.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___403_2555.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___403_2555.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___403_2555.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___403_2555.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___403_2555.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___403_2555.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___403_2555.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___403_2555.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___408_2576 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___408_2576.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___408_2576.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___408_2576.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___408_2576.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___408_2576.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___408_2576.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___408_2576.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___408_2576.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___408_2576.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___408_2576.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___408_2576.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___408_2576.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___413_2597 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___413_2597.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___413_2597.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___413_2597.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___413_2597.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___413_2597.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___413_2597.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___413_2597.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___413_2597.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___413_2597.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___413_2597.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___413_2597.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___413_2597.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2609  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2640 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2640 with
        | (u,ctx_uvar,g_u) ->
            let uu____2678 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2678
              (fun uu____2687  ->
                 let uu____2688 =
                   let uu____2693 =
                     let uu____2694 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2694  in
                   (u, uu____2693)  in
                 ret uu____2688)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2715 = FStar_Syntax_Util.un_squash t1  in
    match uu____2715 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2727 =
          let uu____2728 = FStar_Syntax_Subst.compress t'1  in
          uu____2728.FStar_Syntax_Syntax.n  in
        (match uu____2727 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2733 -> false)
    | uu____2735 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2748 = FStar_Syntax_Util.un_squash t  in
    match uu____2748 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2759 =
          let uu____2760 = FStar_Syntax_Subst.compress t'  in
          uu____2760.FStar_Syntax_Syntax.n  in
        (match uu____2759 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2765 -> false)
    | uu____2767 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2780  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2792 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2792 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2799 = goal_to_string_verbose hd1  in
                    let uu____2801 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2799 uu____2801);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2814 =
      bind get
        (fun ps  ->
           let uu____2820 = cur_goal ()  in
           bind uu____2820
             (fun g  ->
                (let uu____2827 =
                   let uu____2828 = FStar_Tactics_Types.goal_type g  in
                   uu____2828.FStar_Syntax_Syntax.pos  in
                 let uu____2831 =
                   let uu____2837 =
                     let uu____2839 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2839
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2837)  in
                 FStar_Errors.log_issue uu____2827 uu____2831);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2814
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2862  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___458_2873 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___458_2873.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___458_2873.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___458_2873.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___458_2873.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___458_2873.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___458_2873.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___458_2873.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___458_2873.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___458_2873.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___458_2873.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___458_2873.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___458_2873.FStar_Tactics_Types.local_state)
           }  in
         let uu____2875 = set ps1  in
         bind uu____2875
           (fun uu____2880  ->
              let uu____2881 = FStar_BigInt.of_int_fs n1  in ret uu____2881))
  
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
              let uu____2919 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2919 phi  in
            let uu____2920 = new_uvar reason env typ  in
            bind uu____2920
              (fun uu____2935  ->
                 match uu____2935 with
                 | (uu____2942,ctx_uvar) ->
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
             (fun uu____2989  ->
                let uu____2990 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2990)
             (fun uu____2995  ->
                let e1 =
                  let uu___476_2997 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___476_2997.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___476_2997.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___476_2997.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___476_2997.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___476_2997.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___476_2997.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___476_2997.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___476_2997.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___476_2997.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___476_2997.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___476_2997.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___476_2997.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___476_2997.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___476_2997.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___476_2997.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___476_2997.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___476_2997.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___476_2997.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___476_2997.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___476_2997.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___476_2997.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___476_2997.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___476_2997.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___476_2997.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___476_2997.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___476_2997.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___476_2997.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___476_2997.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___476_2997.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___476_2997.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___476_2997.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___476_2997.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___476_2997.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___476_2997.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___476_2997.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___476_2997.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___476_2997.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___476_2997.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___476_2997.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___476_2997.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___476_2997.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___476_2997.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___480_3009  ->
                     match () with
                     | () ->
                         let uu____3018 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3018) ()
                with
                | FStar_Errors.Err (uu____3045,msg) ->
                    let uu____3049 = tts e1 t  in
                    let uu____3051 =
                      let uu____3053 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3053
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3049 uu____3051 msg
                | FStar_Errors.Error (uu____3063,msg,uu____3065) ->
                    let uu____3068 = tts e1 t  in
                    let uu____3070 =
                      let uu____3072 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3072
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3068 uu____3070 msg))
  
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
             (fun uu____3125  ->
                let uu____3126 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3126)
             (fun uu____3131  ->
                let e1 =
                  let uu___497_3133 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___497_3133.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___497_3133.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___497_3133.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___497_3133.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___497_3133.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___497_3133.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___497_3133.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___497_3133.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___497_3133.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___497_3133.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___497_3133.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___497_3133.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___497_3133.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___497_3133.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___497_3133.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___497_3133.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___497_3133.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___497_3133.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___497_3133.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___497_3133.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___497_3133.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___497_3133.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___497_3133.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___497_3133.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___497_3133.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___497_3133.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___497_3133.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___497_3133.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___497_3133.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___497_3133.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___497_3133.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___497_3133.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___497_3133.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___497_3133.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___497_3133.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___497_3133.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___497_3133.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___497_3133.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___497_3133.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___497_3133.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___497_3133.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___497_3133.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___501_3148  ->
                     match () with
                     | () ->
                         let uu____3157 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3157 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3195,msg) ->
                    let uu____3199 = tts e1 t  in
                    let uu____3201 =
                      let uu____3203 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3203
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3199 uu____3201 msg
                | FStar_Errors.Error (uu____3213,msg,uu____3215) ->
                    let uu____3218 = tts e1 t  in
                    let uu____3220 =
                      let uu____3222 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3222
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3218 uu____3220 msg))
  
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
             (fun uu____3275  ->
                let uu____3276 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3276)
             (fun uu____3282  ->
                let e1 =
                  let uu___522_3284 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___522_3284.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___522_3284.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___522_3284.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___522_3284.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___522_3284.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___522_3284.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___522_3284.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___522_3284.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___522_3284.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___522_3284.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___522_3284.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___522_3284.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___522_3284.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___522_3284.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___522_3284.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___522_3284.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___522_3284.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___522_3284.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___522_3284.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___522_3284.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___522_3284.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___522_3284.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___522_3284.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___522_3284.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___522_3284.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___522_3284.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___522_3284.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___522_3284.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___522_3284.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___522_3284.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___522_3284.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___522_3284.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___522_3284.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___522_3284.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___522_3284.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___522_3284.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___522_3284.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___522_3284.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___522_3284.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___522_3284.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___522_3284.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___522_3284.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___525_3287 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___525_3287.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___525_3287.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___525_3287.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___525_3287.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___525_3287.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___525_3287.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___525_3287.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___525_3287.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___525_3287.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___525_3287.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___525_3287.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___525_3287.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___525_3287.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___525_3287.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___525_3287.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___525_3287.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___525_3287.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___525_3287.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___525_3287.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___525_3287.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___525_3287.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___525_3287.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___525_3287.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___525_3287.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___525_3287.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___525_3287.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___525_3287.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___525_3287.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___525_3287.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___525_3287.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___525_3287.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___525_3287.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___525_3287.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___525_3287.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___525_3287.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___525_3287.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___525_3287.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___525_3287.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___525_3287.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___525_3287.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___525_3287.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___525_3287.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___529_3299  ->
                     match () with
                     | () ->
                         let uu____3308 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3308) ()
                with
                | FStar_Errors.Err (uu____3335,msg) ->
                    let uu____3339 = tts e2 t  in
                    let uu____3341 =
                      let uu____3343 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3343
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3339 uu____3341 msg
                | FStar_Errors.Error (uu____3353,msg,uu____3355) ->
                    let uu____3358 = tts e2 t  in
                    let uu____3360 =
                      let uu____3362 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3362
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3358 uu____3360 msg))
  
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
  fun uu____3396  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___550_3415 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___550_3415.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___550_3415.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___550_3415.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___550_3415.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___550_3415.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___550_3415.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___550_3415.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___550_3415.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___550_3415.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___550_3415.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___550_3415.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___550_3415.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3440 = get_guard_policy ()  in
      bind uu____3440
        (fun old_pol  ->
           let uu____3446 = set_guard_policy pol  in
           bind uu____3446
             (fun uu____3450  ->
                bind t
                  (fun r  ->
                     let uu____3454 = set_guard_policy old_pol  in
                     bind uu____3454 (fun uu____3458  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3462 = let uu____3467 = cur_goal ()  in trytac uu____3467  in
  bind uu____3462
    (fun uu___0_3474  ->
       match uu___0_3474 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3480 = FStar_Options.peek ()  in ret uu____3480)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3505  ->
             let uu____3506 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3506)
          (fun uu____3511  ->
             let uu____3512 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3512
               (fun uu____3516  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3520 =
                         let uu____3521 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3521.FStar_TypeChecker_Env.guard_f  in
                       match uu____3520 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3525 = istrivial e f  in
                           if uu____3525
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3538 =
                                          let uu____3544 =
                                            let uu____3546 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3546
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3544)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3538);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3552  ->
                                           let uu____3553 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3553)
                                        (fun uu____3558  ->
                                           let uu____3559 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3559
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___579_3567 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___579_3567.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___579_3567.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___579_3567.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___579_3567.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3571  ->
                                           let uu____3572 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3572)
                                        (fun uu____3577  ->
                                           let uu____3578 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3578
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___586_3586 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___586_3586.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___586_3586.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___586_3586.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___586_3586.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3590  ->
                                           let uu____3591 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3591)
                                        (fun uu____3595  ->
                                           try
                                             (fun uu___593_3600  ->
                                                match () with
                                                | () ->
                                                    let uu____3603 =
                                                      let uu____3605 =
                                                        let uu____3607 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3607
                                                         in
                                                      Prims.op_Negation
                                                        uu____3605
                                                       in
                                                    if uu____3603
                                                    then
                                                      mlog
                                                        (fun uu____3614  ->
                                                           let uu____3615 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3615)
                                                        (fun uu____3619  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___592_3624 ->
                                               mlog
                                                 (fun uu____3629  ->
                                                    let uu____3630 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3630)
                                                 (fun uu____3634  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____3646 =
      let uu____3649 = cur_goal ()  in
      bind uu____3649
        (fun goal  ->
           let uu____3655 =
             let uu____3664 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3664 t  in
           bind uu____3655
             (fun uu____3676  ->
                match uu____3676 with
                | (uu____3685,lc,uu____3687) ->
                    let uu____3688 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____3688))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____3646
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3704 =
      let uu____3709 = tcc t  in
      bind uu____3709 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3704
  
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
            let uu____3761 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3761 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3773  ->
    let uu____3776 = cur_goal ()  in
    bind uu____3776
      (fun goal  ->
         let uu____3782 =
           let uu____3784 = FStar_Tactics_Types.goal_env goal  in
           let uu____3785 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3784 uu____3785  in
         if uu____3782
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3791 =
              let uu____3793 = FStar_Tactics_Types.goal_env goal  in
              let uu____3794 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3793 uu____3794  in
            fail1 "Not a trivial goal: %s" uu____3791))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3845 =
               try
                 (fun uu___651_3868  ->
                    match () with
                    | () ->
                        let uu____3879 =
                          let uu____3888 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3888
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3879) ()
               with | uu___650_3899 -> fail "divide: not enough goals"  in
             bind uu____3845
               (fun uu____3936  ->
                  match uu____3936 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___633_3962 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___633_3962.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___633_3962.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___633_3962.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___633_3962.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___633_3962.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___633_3962.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___633_3962.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___633_3962.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___633_3962.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___633_3962.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___633_3962.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3963 = set lp  in
                      bind uu____3963
                        (fun uu____3971  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___639_3987 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___639_3987.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___639_3987.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___639_3987.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___639_3987.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___639_3987.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___639_3987.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___639_3987.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___639_3987.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___639_3987.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___639_3987.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___639_3987.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3988 = set rp  in
                                     bind uu____3988
                                       (fun uu____3996  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___645_4012 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___645_4012.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___645_4012.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4013 = set p'
                                                       in
                                                    bind uu____4013
                                                      (fun uu____4021  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4027 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4049 = divide FStar_BigInt.one f idtac  in
    bind uu____4049
      (fun uu____4062  -> match uu____4062 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4100::uu____4101 ->
             let uu____4104 =
               let uu____4113 = map tau  in
               divide FStar_BigInt.one tau uu____4113  in
             bind uu____4104
               (fun uu____4131  ->
                  match uu____4131 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4173 =
        bind t1
          (fun uu____4178  ->
             let uu____4179 = map t2  in
             bind uu____4179 (fun uu____4187  -> ret ()))
         in
      focus uu____4173
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4197  ->
    let uu____4200 =
      let uu____4203 = cur_goal ()  in
      bind uu____4203
        (fun goal  ->
           let uu____4212 =
             let uu____4219 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4219  in
           match uu____4212 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4228 =
                 let uu____4230 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4230  in
               if uu____4228
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4239 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4239 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4255 = new_uvar "intro" env' typ'  in
                  bind uu____4255
                    (fun uu____4272  ->
                       match uu____4272 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4296 = set_solution goal sol  in
                           bind uu____4296
                             (fun uu____4302  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4304 =
                                  let uu____4307 = bnorm_goal g  in
                                  replace_cur uu____4307  in
                                bind uu____4304 (fun uu____4309  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4314 =
                 let uu____4316 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4317 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4316 uu____4317  in
               fail1 "goal is not an arrow (%s)" uu____4314)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4200
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4335  ->
    let uu____4342 = cur_goal ()  in
    bind uu____4342
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4361 =
            let uu____4368 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4368  in
          match uu____4361 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4381 =
                let uu____4383 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4383  in
              if uu____4381
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4400 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4400
                    in
                 let bs =
                   let uu____4411 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4411; b]  in
                 let env' =
                   let uu____4437 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4437 bs  in
                 let uu____4438 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4438
                   (fun uu____4464  ->
                      match uu____4464 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4478 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4481 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4478
                              FStar_Parser_Const.effect_Tot_lid uu____4481 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4499 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4499 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4521 =
                                   let uu____4522 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4522.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4521
                                  in
                               let uu____4538 = set_solution goal tm  in
                               bind uu____4538
                                 (fun uu____4547  ->
                                    let uu____4548 =
                                      let uu____4551 =
                                        bnorm_goal
                                          (let uu___716_4554 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___716_4554.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___716_4554.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___716_4554.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___716_4554.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4551  in
                                    bind uu____4548
                                      (fun uu____4561  ->
                                         let uu____4562 =
                                           let uu____4567 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4567, b)  in
                                         ret uu____4562)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4576 =
                let uu____4578 = FStar_Tactics_Types.goal_env goal  in
                let uu____4579 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4578 uu____4579  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4576))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4599 = cur_goal ()  in
    bind uu____4599
      (fun goal  ->
         mlog
           (fun uu____4606  ->
              let uu____4607 =
                let uu____4609 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4609  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4607)
           (fun uu____4615  ->
              let steps =
                let uu____4619 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4619
                 in
              let t =
                let uu____4623 = FStar_Tactics_Types.goal_env goal  in
                let uu____4624 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4623 uu____4624  in
              let uu____4625 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4625))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4650 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4658 -> g.FStar_Tactics_Types.opts
                 | uu____4661 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4666  ->
                    let uu____4667 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4667)
                 (fun uu____4672  ->
                    let uu____4673 = __tc_lax e t  in
                    bind uu____4673
                      (fun uu____4694  ->
                         match uu____4694 with
                         | (t1,uu____4704,uu____4705) ->
                             let steps =
                               let uu____4709 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4709
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4715  ->
                                  let uu____4716 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4716)
                               (fun uu____4720  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4650
  
let (refine_intro : unit -> unit tac) =
  fun uu____4733  ->
    let uu____4736 =
      let uu____4739 = cur_goal ()  in
      bind uu____4739
        (fun g  ->
           let uu____4746 =
             let uu____4757 = FStar_Tactics_Types.goal_env g  in
             let uu____4758 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4757 uu____4758
              in
           match uu____4746 with
           | (uu____4761,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4787 =
                 let uu____4792 =
                   let uu____4797 =
                     let uu____4798 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4798]  in
                   FStar_Syntax_Subst.open_term uu____4797 phi  in
                 match uu____4792 with
                 | (bvs,phi1) ->
                     let uu____4823 =
                       let uu____4824 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4824  in
                     (uu____4823, phi1)
                  in
               (match uu____4787 with
                | (bv1,phi1) ->
                    let uu____4843 =
                      let uu____4846 = FStar_Tactics_Types.goal_env g  in
                      let uu____4847 =
                        let uu____4848 =
                          let uu____4851 =
                            let uu____4852 =
                              let uu____4859 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4859)  in
                            FStar_Syntax_Syntax.NT uu____4852  in
                          [uu____4851]  in
                        FStar_Syntax_Subst.subst uu____4848 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4846
                        uu____4847 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4843
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4868  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4736
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4891 = cur_goal ()  in
      bind uu____4891
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4900 = FStar_Tactics_Types.goal_env goal  in
               let uu____4901 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4900 uu____4901
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4904 = __tc env t  in
           bind uu____4904
             (fun uu____4923  ->
                match uu____4923 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4938  ->
                         let uu____4939 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4941 =
                           let uu____4943 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4943
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4939 uu____4941)
                      (fun uu____4947  ->
                         let uu____4948 =
                           let uu____4951 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4951 guard  in
                         bind uu____4948
                           (fun uu____4954  ->
                              mlog
                                (fun uu____4958  ->
                                   let uu____4959 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4961 =
                                     let uu____4963 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4963
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4959 uu____4961)
                                (fun uu____4967  ->
                                   let uu____4968 =
                                     let uu____4972 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4973 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4972 typ uu____4973  in
                                   bind uu____4968
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4983 =
                                             let uu____4985 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4985 t1  in
                                           let uu____4986 =
                                             let uu____4988 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4988 typ  in
                                           let uu____4989 =
                                             let uu____4991 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4992 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4991 uu____4992  in
                                           let uu____4993 =
                                             let uu____4995 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4996 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4995 uu____4996  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4983 uu____4986 uu____4989
                                             uu____4993)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5022 =
          mlog
            (fun uu____5027  ->
               let uu____5028 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5028)
            (fun uu____5033  ->
               let uu____5034 =
                 let uu____5041 = __exact_now set_expected_typ1 tm  in
                 catch uu____5041  in
               bind uu____5034
                 (fun uu___2_5050  ->
                    match uu___2_5050 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5061  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5065  ->
                             let uu____5066 =
                               let uu____5073 =
                                 let uu____5076 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5076
                                   (fun uu____5081  ->
                                      let uu____5082 = refine_intro ()  in
                                      bind uu____5082
                                        (fun uu____5086  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5073  in
                             bind uu____5066
                               (fun uu___1_5093  ->
                                  match uu___1_5093 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5102  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5105  -> ret ())
                                  | FStar_Util.Inl uu____5106 ->
                                      mlog
                                        (fun uu____5108  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5111  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5022
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5163 = f x  in
          bind uu____5163
            (fun y  ->
               let uu____5171 = mapM f xs  in
               bind uu____5171 (fun ys  -> ret (y :: ys)))
  
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
          let uu____5243 = do_unify e ty1 ty2  in
          bind uu____5243
            (fun uu___3_5257  ->
               if uu___3_5257
               then ret acc
               else
                 (let uu____5277 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____5277 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____5298 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____5300 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____5298
                        uu____5300
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____5317 =
                        let uu____5319 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____5319  in
                      if uu____5317
                      then fail "Codomain is effectful"
                      else
                        (let uu____5343 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____5343
                           (fun uu____5370  ->
                              match uu____5370 with
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
      let uu____5462 =
        mlog
          (fun uu____5467  ->
             let uu____5468 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5468)
          (fun uu____5473  ->
             let uu____5474 = cur_goal ()  in
             bind uu____5474
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5482 = __tc e tm  in
                  bind uu____5482
                    (fun uu____5503  ->
                       match uu____5503 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5516 =
                             let uu____5527 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5527  in
                           bind uu____5516
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____5565)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____5569 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5592  ->
                                       fun w  ->
                                         match uu____5592 with
                                         | (uvt,q,uu____5610) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5642 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5659  ->
                                       fun s  ->
                                         match uu____5659 with
                                         | (uu____5671,uu____5672,uv) ->
                                             let uu____5674 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5674) uvs uu____5642
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5684 = solve' goal w  in
                                bind uu____5684
                                  (fun uu____5689  ->
                                     let uu____5690 =
                                       mapM
                                         (fun uu____5707  ->
                                            match uu____5707 with
                                            | (uvt,q,uv) ->
                                                let uu____5719 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5719 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5724 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5725 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5725
                                                     then ret ()
                                                     else
                                                       (let uu____5732 =
                                                          let uu____5735 =
                                                            bnorm_goal
                                                              (let uu___877_5738
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___877_5738.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___877_5738.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___877_5738.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5735]  in
                                                        add_goals uu____5732)))
                                         uvs
                                        in
                                     bind uu____5690
                                       (fun uu____5743  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5462
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5771 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5771
    then
      let uu____5780 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5795 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5848 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5780 with
      | (pre,post) ->
          let post1 =
            let uu____5881 =
              let uu____5892 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5892]  in
            FStar_Syntax_Util.mk_app post uu____5881  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5923 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5923
       then
         let uu____5932 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5932
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
            let uu____6011 = f x e  in
            bind uu____6011 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6026 =
      let uu____6029 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6036  ->
                  let uu____6037 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6037)
               (fun uu____6043  ->
                  let is_unit_t t =
                    let uu____6051 =
                      let uu____6052 = FStar_Syntax_Subst.compress t  in
                      uu____6052.FStar_Syntax_Syntax.n  in
                    match uu____6051 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6058 -> false  in
                  let uu____6060 = cur_goal ()  in
                  bind uu____6060
                    (fun goal  ->
                       let uu____6066 =
                         let uu____6075 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6075 tm  in
                       bind uu____6066
                         (fun uu____6090  ->
                            match uu____6090 with
                            | (tm1,t,guard) ->
                                let uu____6102 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6102 with
                                 | (bs,comp) ->
                                     let uu____6135 = lemma_or_sq comp  in
                                     (match uu____6135 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6155 =
                                            fold_left
                                              (fun uu____6217  ->
                                                 fun uu____6218  ->
                                                   match (uu____6217,
                                                           uu____6218)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6369 =
                                                         is_unit_t b_t  in
                                                       if uu____6369
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
                                                         (let uu____6492 =
                                                            let uu____6499 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6499 b_t
                                                             in
                                                          bind uu____6492
                                                            (fun uu____6530 
                                                               ->
                                                               match uu____6530
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
                                          bind uu____6155
                                            (fun uu____6716  ->
                                               match uu____6716 with
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
                                                   let uu____6804 =
                                                     let uu____6808 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6809 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6810 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6808
                                                       uu____6809 uu____6810
                                                      in
                                                   bind uu____6804
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6821 =
                                                            let uu____6823 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6823
                                                              tm1
                                                             in
                                                          let uu____6824 =
                                                            let uu____6826 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6827 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____6826
                                                              uu____6827
                                                             in
                                                          let uu____6828 =
                                                            let uu____6830 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6831 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6830
                                                              uu____6831
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6821
                                                            uu____6824
                                                            uu____6828
                                                        else
                                                          (let uu____6835 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6835
                                                             (fun uu____6843 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____6869
                                                                    =
                                                                    let uu____6872
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6872
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6869
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
                                                                    let uu____6908
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6908)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____6925
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____6925
                                                                  with
                                                                  | (hd1,uu____6944)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6971)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6988
                                                                    -> false)
                                                                   in
                                                                let uu____6990
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
                                                                    let uu____7033
                                                                    = imp  in
                                                                    match uu____7033
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7044
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7044
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7066)
                                                                    ->
                                                                    let uu____7091
                                                                    =
                                                                    let uu____7092
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7092.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7091
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7100)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___987_7120
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___987_7120.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___987_7120.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___987_7120.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___987_7120.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7123
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7129
                                                                     ->
                                                                    let uu____7130
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7132
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7130
                                                                    uu____7132)
                                                                    (fun
                                                                    uu____7139
                                                                     ->
                                                                    let env =
                                                                    let uu___992_7141
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___992_7141.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7144
                                                                    =
                                                                    let uu____7147
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7151
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7153
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7151
                                                                    uu____7153
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7159
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7147
                                                                    uu____7159
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7144
                                                                    (fun
                                                                    uu____7163
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____6990
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
                                                                    let uu____7227
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7227
                                                                    then
                                                                    let uu____7232
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7232
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
                                                                    let uu____7247
                                                                    =
                                                                    let uu____7249
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7249
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7247)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7250
                                                                    =
                                                                    let uu____7253
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7253
                                                                    guard  in
                                                                    bind
                                                                    uu____7250
                                                                    (fun
                                                                    uu____7257
                                                                     ->
                                                                    let uu____7258
                                                                    =
                                                                    let uu____7261
                                                                    =
                                                                    let uu____7263
                                                                    =
                                                                    let uu____7265
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7266
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7265
                                                                    uu____7266
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7263
                                                                     in
                                                                    if
                                                                    uu____7261
                                                                    then
                                                                    let uu____7270
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7270
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7258
                                                                    (fun
                                                                    uu____7275
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6029  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6026
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7299 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7299 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7309::(e1,uu____7311)::(e2,uu____7313)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____7374 ->
        let uu____7377 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7377 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____7392 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____7392);
              (let uu____7395 = FStar_Syntax_Util.head_and_args t  in
               match uu____7395 with
               | (hd1,args) ->
                   let uu____7444 =
                     let uu____7459 =
                       let uu____7460 = FStar_Syntax_Subst.compress hd1  in
                       uu____7460.FStar_Syntax_Syntax.n  in
                     (uu____7459, args)  in
                   (match uu____7444 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____7480,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____7481))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____7546 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____7548 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____7546
                            uu____7548);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____7555 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7592 = destruct_eq' typ  in
    match uu____7592 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7622 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7622 with
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
        let uu____7691 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7691 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7749 = aux e'  in
               FStar_Util.map_opt uu____7749
                 (fun uu____7780  ->
                    match uu____7780 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7806 = aux e  in
      FStar_Util.map_opt uu____7806
        (fun uu____7837  ->
           match uu____7837 with
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
          let uu____7911 =
            let uu____7922 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____7922  in
          FStar_Util.map_opt uu____7911
            (fun uu____7940  ->
               match uu____7940 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1089_7962 = bv  in
                     let uu____7963 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1089_7962.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1089_7962.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7963
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1093_7971 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7972 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7981 =
                       let uu____7984 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7984  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1093_7971.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7972;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7981;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1093_7971.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1093_7971.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1093_7971.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1093_7971.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1096_7985 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1096_7985.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1096_7985.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1096_7985.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1096_7985.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7996 =
      let uu____7999 = cur_goal ()  in
      bind uu____7999
        (fun goal  ->
           let uu____8007 = h  in
           match uu____8007 with
           | (bv,uu____8011) ->
               mlog
                 (fun uu____8019  ->
                    let uu____8020 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8022 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8020
                      uu____8022)
                 (fun uu____8027  ->
                    let uu____8028 =
                      let uu____8039 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8039  in
                    match uu____8028 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8066 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8066 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8081 =
                               let uu____8082 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8082.FStar_Syntax_Syntax.n  in
                             (match uu____8081 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1119_8099 = bv2  in
                                    let uu____8100 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1119_8099.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1119_8099.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8100
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1123_8108 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8109 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8118 =
                                      let uu____8121 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8121
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1123_8108.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8109;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8118;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1123_8108.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1123_8108.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1123_8108.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1123_8108.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1126_8124 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1126_8124.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1126_8124.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1126_8124.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1126_8124.FStar_Tactics_Types.label)
                                     })
                              | uu____8125 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8127 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7996
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____8157 =
        let uu____8160 = cur_goal ()  in
        bind uu____8160
          (fun goal  ->
             let uu____8171 = b  in
             match uu____8171 with
             | (bv,uu____8175) ->
                 let bv' =
                   let uu____8181 =
                     let uu___1137_8182 = bv  in
                     let uu____8183 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8183;
                       FStar_Syntax_Syntax.index =
                         (uu___1137_8182.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1137_8182.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8181  in
                 let s1 =
                   let uu____8188 =
                     let uu____8189 =
                       let uu____8196 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8196)  in
                     FStar_Syntax_Syntax.NT uu____8189  in
                   [uu____8188]  in
                 let uu____8201 = subst_goal bv bv' s1 goal  in
                 (match uu____8201 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8157
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8223 =
      let uu____8226 = cur_goal ()  in
      bind uu____8226
        (fun goal  ->
           let uu____8235 = b  in
           match uu____8235 with
           | (bv,uu____8239) ->
               let uu____8244 =
                 let uu____8255 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8255  in
               (match uu____8244 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8282 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8282 with
                     | (ty,u) ->
                         let uu____8291 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8291
                           (fun uu____8310  ->
                              match uu____8310 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1161_8320 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1161_8320.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1161_8320.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8324 =
                                      let uu____8325 =
                                        let uu____8332 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8332)  in
                                      FStar_Syntax_Syntax.NT uu____8325  in
                                    [uu____8324]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1166_8344 = b1  in
                                         let uu____8345 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1166_8344.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1166_8344.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8345
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8352  ->
                                       let new_goal =
                                         let uu____8354 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8355 =
                                           let uu____8356 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8356
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8354 uu____8355
                                          in
                                       let uu____8357 = add_goals [new_goal]
                                          in
                                       bind uu____8357
                                         (fun uu____8362  ->
                                            let uu____8363 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8363
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8223
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8389 =
        let uu____8392 = cur_goal ()  in
        bind uu____8392
          (fun goal  ->
             let uu____8401 = b  in
             match uu____8401 with
             | (bv,uu____8405) ->
                 let uu____8410 =
                   let uu____8421 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8421  in
                 (match uu____8410 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8451 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8451
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1187_8456 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1187_8456.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1187_8456.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8458 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8458))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8389
  
let (revert : unit -> unit tac) =
  fun uu____8471  ->
    let uu____8474 = cur_goal ()  in
    bind uu____8474
      (fun goal  ->
         let uu____8480 =
           let uu____8487 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8487  in
         match uu____8480 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8504 =
                 let uu____8507 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8507  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8504
                in
             let uu____8522 = new_uvar "revert" env' typ'  in
             bind uu____8522
               (fun uu____8538  ->
                  match uu____8538 with
                  | (r,u_r) ->
                      let uu____8547 =
                        let uu____8550 =
                          let uu____8551 =
                            let uu____8552 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8552.FStar_Syntax_Syntax.pos  in
                          let uu____8555 =
                            let uu____8560 =
                              let uu____8561 =
                                let uu____8570 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8570  in
                              [uu____8561]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8560  in
                          uu____8555 FStar_Pervasives_Native.None uu____8551
                           in
                        set_solution goal uu____8550  in
                      bind uu____8547
                        (fun uu____8589  ->
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
      let uu____8603 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8603
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8619 = cur_goal ()  in
    bind uu____8619
      (fun goal  ->
         mlog
           (fun uu____8627  ->
              let uu____8628 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8630 =
                let uu____8632 =
                  let uu____8634 =
                    let uu____8643 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8643  in
                  FStar_All.pipe_right uu____8634 FStar_List.length  in
                FStar_All.pipe_right uu____8632 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8628 uu____8630)
           (fun uu____8664  ->
              let uu____8665 =
                let uu____8676 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8676  in
              match uu____8665 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8721 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8721
                        then
                          let uu____8726 =
                            let uu____8728 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8728
                             in
                          fail uu____8726
                        else check1 bvs2
                     in
                  let uu____8733 =
                    let uu____8735 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8735  in
                  if uu____8733
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8742 = check1 bvs  in
                     bind uu____8742
                       (fun uu____8748  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8750 =
                            let uu____8757 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8757  in
                          bind uu____8750
                            (fun uu____8767  ->
                               match uu____8767 with
                               | (ut,uvar_ut) ->
                                   let uu____8776 = set_solution goal ut  in
                                   bind uu____8776
                                     (fun uu____8781  ->
                                        let uu____8782 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8782))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8790  ->
    let uu____8793 = cur_goal ()  in
    bind uu____8793
      (fun goal  ->
         let uu____8799 =
           let uu____8806 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8806  in
         match uu____8799 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8815) ->
             let uu____8820 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8820)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8833 = cur_goal ()  in
    bind uu____8833
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8843 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8843  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8846  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____8859 = cur_goal ()  in
    bind uu____8859
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8869 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8869  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8872  -> add_goals [g']))
  
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
            let uu____8913 = FStar_Syntax_Subst.compress t  in
            uu____8913.FStar_Syntax_Syntax.n  in
          let uu____8916 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1371_8923 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1371_8923.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1371_8923.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____8916
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____8940 =
                   let uu____8941 = FStar_Syntax_Subst.compress t1  in
                   uu____8941.FStar_Syntax_Syntax.n  in
                 match uu____8940 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8972 = ff hd1  in
                     bind uu____8972
                       (fun hd2  ->
                          let fa uu____8998 =
                            match uu____8998 with
                            | (a,q) ->
                                let uu____9019 = ff a  in
                                bind uu____9019 (fun a1  -> ret (a1, q))
                             in
                          let uu____9038 = mapM fa args  in
                          bind uu____9038
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9120 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9120 with
                      | (bs1,t') ->
                          let uu____9129 =
                            let uu____9132 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9132 t'  in
                          bind uu____9129
                            (fun t''  ->
                               let uu____9136 =
                                 let uu____9137 =
                                   let uu____9156 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9165 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9156, uu____9165, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9137  in
                               ret uu____9136))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9240 = ff hd1  in
                     bind uu____9240
                       (fun hd2  ->
                          let ffb br =
                            let uu____9255 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9255 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9287 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9287  in
                                let uu____9288 = ff1 e  in
                                bind uu____9288
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9303 = mapM ffb brs  in
                          bind uu____9303
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9347;
                          FStar_Syntax_Syntax.lbtyp = uu____9348;
                          FStar_Syntax_Syntax.lbeff = uu____9349;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9351;
                          FStar_Syntax_Syntax.lbpos = uu____9352;_}::[]),e)
                     ->
                     let lb =
                       let uu____9380 =
                         let uu____9381 = FStar_Syntax_Subst.compress t1  in
                         uu____9381.FStar_Syntax_Syntax.n  in
                       match uu____9380 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9385) -> lb
                       | uu____9401 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9411 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9411
                         (fun def1  ->
                            ret
                              (let uu___1324_9417 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1324_9417.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1324_9417.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1324_9417.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1324_9417.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1324_9417.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1324_9417.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9418 = fflb lb  in
                     bind uu____9418
                       (fun lb1  ->
                          let uu____9428 =
                            let uu____9433 =
                              let uu____9434 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9434]  in
                            FStar_Syntax_Subst.open_term uu____9433 e  in
                          match uu____9428 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9464 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9464  in
                              let uu____9465 = ff1 e1  in
                              bind uu____9465
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9512 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9512
                         (fun def  ->
                            ret
                              (let uu___1342_9518 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1342_9518.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1342_9518.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1342_9518.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1342_9518.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1342_9518.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1342_9518.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9519 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9519 with
                      | (lbs1,e1) ->
                          let uu____9534 = mapM fflb lbs1  in
                          bind uu____9534
                            (fun lbs2  ->
                               let uu____9546 = ff e1  in
                               bind uu____9546
                                 (fun e2  ->
                                    let uu____9554 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9554 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9625 = ff t2  in
                     bind uu____9625
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9656 = ff t2  in
                     bind uu____9656
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9663 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1366_9670 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1366_9670.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1366_9670.FStar_Syntax_Syntax.vars)
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
              let uu____9717 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1379_9726 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1379_9726.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1379_9726.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1379_9726.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1379_9726.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1379_9726.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1379_9726.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1379_9726.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1379_9726.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1379_9726.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1379_9726.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1379_9726.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1379_9726.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1379_9726.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1379_9726.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1379_9726.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1379_9726.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1379_9726.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1379_9726.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1379_9726.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1379_9726.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1379_9726.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1379_9726.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1379_9726.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1379_9726.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1379_9726.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1379_9726.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1379_9726.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1379_9726.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1379_9726.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1379_9726.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1379_9726.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1379_9726.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1379_9726.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1379_9726.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1379_9726.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1379_9726.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1379_9726.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1379_9726.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1379_9726.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1379_9726.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1379_9726.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1379_9726.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9717 with
              | (t1,lcomp,g) ->
                  let uu____9733 =
                    (let uu____9737 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9737) ||
                      (let uu____9740 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9740)
                     in
                  if uu____9733
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9751 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9751
                         (fun uu____9768  ->
                            match uu____9768 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9781  ->
                                      let uu____9782 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9784 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9782 uu____9784);
                                 (let uu____9787 =
                                    let uu____9790 =
                                      let uu____9791 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9791 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9790
                                      opts label1
                                     in
                                  bind uu____9787
                                    (fun uu____9795  ->
                                       let uu____9796 =
                                         bind tau
                                           (fun uu____9802  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9808  ->
                                                   let uu____9809 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9811 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9809 uu____9811);
                                              ret ut1)
                                          in
                                       focus uu____9796))))
                        in
                     let uu____9814 = catch rewrite_eq  in
                     bind uu____9814
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
          let uu____10026 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10026
            (fun t1  ->
               let uu____10034 =
                 f env
                   (let uu___1456_10042 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1456_10042.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1456_10042.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10034
                 (fun uu____10058  ->
                    match uu____10058 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10081 =
                               let uu____10082 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10082.FStar_Syntax_Syntax.n  in
                             match uu____10081 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10119 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10119
                                   (fun uu____10141  ->
                                      match uu____10141 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10157 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10157
                                            (fun uu____10181  ->
                                               match uu____10181 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1436_10211 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1436_10211.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1436_10211.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10253 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10253 with
                                  | (bs1,t') ->
                                      let uu____10268 =
                                        let uu____10275 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10275 ctrl1 t'
                                         in
                                      bind uu____10268
                                        (fun uu____10290  ->
                                           match uu____10290 with
                                           | (t'',ctrl2) ->
                                               let uu____10305 =
                                                 let uu____10312 =
                                                   let uu___1449_10315 = t4
                                                      in
                                                   let uu____10318 =
                                                     let uu____10319 =
                                                       let uu____10338 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10347 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10338,
                                                         uu____10347, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10319
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10318;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1449_10315.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1449_10315.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10312, ctrl2)  in
                                               ret uu____10305))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10400 -> ret (t3, ctrl1))))

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
              let uu____10446 = ctrl_tac_fold f env ctrl t  in
              bind uu____10446
                (fun uu____10467  ->
                   match uu____10467 with
                   | (t1,ctrl1) ->
                       let uu____10482 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10482
                         (fun uu____10506  ->
                            match uu____10506 with
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
                let uu____10597 =
                  let uu____10605 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10605
                    (fun uu____10616  ->
                       let uu____10617 = ctrl t1  in
                       bind uu____10617
                         (fun res  ->
                            let uu____10643 = trivial ()  in
                            bind uu____10643 (fun uu____10652  -> ret res)))
                   in
                bind uu____10597
                  (fun uu____10670  ->
                     match uu____10670 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10699 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1486_10708 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1486_10708.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1486_10708.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1486_10708.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1486_10708.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1486_10708.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1486_10708.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1486_10708.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1486_10708.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1486_10708.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1486_10708.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1486_10708.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1486_10708.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1486_10708.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1486_10708.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1486_10708.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1486_10708.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1486_10708.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1486_10708.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1486_10708.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1486_10708.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1486_10708.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1486_10708.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1486_10708.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1486_10708.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1486_10708.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1486_10708.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1486_10708.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1486_10708.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1486_10708.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1486_10708.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1486_10708.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1486_10708.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1486_10708.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1486_10708.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1486_10708.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1486_10708.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1486_10708.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1486_10708.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1486_10708.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1486_10708.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1486_10708.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1486_10708.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10699 with
                            | (t2,lcomp,g) ->
                                let uu____10719 =
                                  (let uu____10723 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10723) ||
                                    (let uu____10726 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10726)
                                   in
                                if uu____10719
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10742 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10742
                                     (fun uu____10763  ->
                                        match uu____10763 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10780  ->
                                                  let uu____10781 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10783 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10781 uu____10783);
                                             (let uu____10786 =
                                                let uu____10789 =
                                                  let uu____10790 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10790 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10789 opts label1
                                                 in
                                              bind uu____10786
                                                (fun uu____10798  ->
                                                   let uu____10799 =
                                                     bind rewriter
                                                       (fun uu____10813  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10819 
                                                               ->
                                                               let uu____10820
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10822
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10820
                                                                 uu____10822);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10799)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____10867 =
        bind get
          (fun ps  ->
             let uu____10877 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10877 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10915  ->
                       let uu____10916 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10916);
                  bind dismiss_all
                    (fun uu____10921  ->
                       let uu____10922 =
                         let uu____10929 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10929
                           keepGoing gt1
                          in
                       bind uu____10922
                         (fun uu____10939  ->
                            match uu____10939 with
                            | (gt',uu____10947) ->
                                (log ps
                                   (fun uu____10951  ->
                                      let uu____10952 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10952);
                                 (let uu____10955 = push_goals gs  in
                                  bind uu____10955
                                    (fun uu____10960  ->
                                       let uu____10961 =
                                         let uu____10964 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10964]  in
                                       add_goals uu____10961)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10867
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10989 =
        bind get
          (fun ps  ->
             let uu____10999 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10999 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11037  ->
                       let uu____11038 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11038);
                  bind dismiss_all
                    (fun uu____11043  ->
                       let uu____11044 =
                         let uu____11047 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11047 gt1
                          in
                       bind uu____11044
                         (fun gt'  ->
                            log ps
                              (fun uu____11055  ->
                                 let uu____11056 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11056);
                            (let uu____11059 = push_goals gs  in
                             bind uu____11059
                               (fun uu____11064  ->
                                  let uu____11065 =
                                    let uu____11068 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11068]  in
                                  add_goals uu____11065))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10989
  
let (trefl : unit -> unit tac) =
  fun uu____11081  ->
    let uu____11084 =
      let uu____11087 = cur_goal ()  in
      bind uu____11087
        (fun g  ->
           let uu____11105 =
             let uu____11110 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____11110  in
           match uu____11105 with
           | FStar_Pervasives_Native.Some t ->
               let uu____11118 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____11118 with
                | (hd1,args) ->
                    let uu____11157 =
                      let uu____11170 =
                        let uu____11171 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____11171.FStar_Syntax_Syntax.n  in
                      (uu____11170, args)  in
                    (match uu____11157 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____11185::(l,uu____11187)::(r,uu____11189)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____11236 =
                           let uu____11240 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____11240 l r  in
                         bind uu____11236
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____11251 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11251 l
                                    in
                                 let r1 =
                                   let uu____11253 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11253 r
                                    in
                                 let uu____11254 =
                                   let uu____11258 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____11258 l1 r1  in
                                 bind uu____11254
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____11268 =
                                           let uu____11270 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11270 l1  in
                                         let uu____11271 =
                                           let uu____11273 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11273 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____11268 uu____11271))))
                     | (hd2,uu____11276) ->
                         let uu____11293 =
                           let uu____11295 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____11295 t  in
                         fail1 "trefl: not an equality (%s)" uu____11293))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11084
  
let (dup : unit -> unit tac) =
  fun uu____11312  ->
    let uu____11315 = cur_goal ()  in
    bind uu____11315
      (fun g  ->
         let uu____11321 =
           let uu____11328 = FStar_Tactics_Types.goal_env g  in
           let uu____11329 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11328 uu____11329  in
         bind uu____11321
           (fun uu____11339  ->
              match uu____11339 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1578_11349 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1578_11349.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1578_11349.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1578_11349.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1578_11349.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11352  ->
                       let uu____11353 =
                         let uu____11356 = FStar_Tactics_Types.goal_env g  in
                         let uu____11357 =
                           let uu____11358 =
                             let uu____11359 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11360 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11359
                               uu____11360
                              in
                           let uu____11361 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11362 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11358 uu____11361 u
                             uu____11362
                            in
                         add_irrelevant_goal "dup equation" uu____11356
                           uu____11357 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11353
                         (fun uu____11366  ->
                            let uu____11367 = add_goals [g']  in
                            bind uu____11367 (fun uu____11371  -> ret ())))))
  
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
              let uu____11497 = f x y  in
              if uu____11497 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11520 -> (acc, l11, l21)  in
        let uu____11535 = aux [] l1 l2  in
        match uu____11535 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11641 = get_phi g1  in
      match uu____11641 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11648 = get_phi g2  in
          (match uu____11648 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11661 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11661 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11692 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11692 phi1  in
                    let t2 =
                      let uu____11702 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11702 phi2  in
                    let uu____11711 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11711
                      (fun uu____11716  ->
                         let uu____11717 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11717
                           (fun uu____11724  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1629_11729 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11730 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1629_11729.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1629_11729.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1629_11729.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1629_11729.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11730;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1629_11729.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1629_11729.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1629_11729.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1629_11729.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1629_11729.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1629_11729.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1629_11729.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1629_11729.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1629_11729.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1629_11729.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1629_11729.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1629_11729.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1629_11729.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1629_11729.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1629_11729.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1629_11729.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1629_11729.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1629_11729.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1629_11729.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1629_11729.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1629_11729.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1629_11729.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1629_11729.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1629_11729.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1629_11729.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1629_11729.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1629_11729.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1629_11729.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1629_11729.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1629_11729.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1629_11729.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1629_11729.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1629_11729.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1629_11729.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1629_11729.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1629_11729.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1629_11729.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11734 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11734
                                (fun goal  ->
                                   mlog
                                     (fun uu____11744  ->
                                        let uu____11745 =
                                          goal_to_string_verbose g1  in
                                        let uu____11747 =
                                          goal_to_string_verbose g2  in
                                        let uu____11749 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11745 uu____11747 uu____11749)
                                     (fun uu____11753  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11761  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11777 =
               set
                 (let uu___1644_11782 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1644_11782.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1644_11782.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1644_11782.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1644_11782.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1644_11782.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1644_11782.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1644_11782.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1644_11782.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1644_11782.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1644_11782.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1644_11782.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1644_11782.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11777
               (fun uu____11785  ->
                  let uu____11786 = join_goals g1 g2  in
                  bind uu____11786 (fun g12  -> add_goals [g12]))
         | uu____11791 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11807 =
      let uu____11810 = cur_goal ()  in
      bind uu____11810
        (fun g  ->
           FStar_Options.push ();
           (let uu____11823 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11823);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1655_11830 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1655_11830.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1655_11830.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1655_11830.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1655_11830.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11807
  
let (top_env : unit -> env tac) =
  fun uu____11847  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11862  ->
    let uu____11866 = cur_goal ()  in
    bind uu____11866
      (fun g  ->
         let uu____11873 =
           (FStar_Options.lax ()) ||
             (let uu____11876 = FStar_Tactics_Types.goal_env g  in
              uu____11876.FStar_TypeChecker_Env.lax)
            in
         ret uu____11873)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11893 =
        mlog
          (fun uu____11898  ->
             let uu____11899 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11899)
          (fun uu____11904  ->
             let uu____11905 = cur_goal ()  in
             bind uu____11905
               (fun goal  ->
                  let env =
                    let uu____11913 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11913 ty  in
                  let uu____11914 = __tc_ghost env tm  in
                  bind uu____11914
                    (fun uu____11933  ->
                       match uu____11933 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11947  ->
                                let uu____11948 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11948)
                             (fun uu____11952  ->
                                mlog
                                  (fun uu____11955  ->
                                     let uu____11956 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11956)
                                  (fun uu____11961  ->
                                     let uu____11962 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11962
                                       (fun uu____11967  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11893
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11992 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11998 =
              let uu____12005 =
                let uu____12006 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12006
                 in
              new_uvar "uvar_env.2" env uu____12005  in
            bind uu____11998
              (fun uu____12023  ->
                 match uu____12023 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11992
        (fun typ  ->
           let uu____12035 = new_uvar "uvar_env" env typ  in
           bind uu____12035
             (fun uu____12050  ->
                match uu____12050 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12069 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12088 -> g.FStar_Tactics_Types.opts
             | uu____12091 -> FStar_Options.peek ()  in
           let uu____12094 = FStar_Syntax_Util.head_and_args t  in
           match uu____12094 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12114);
                FStar_Syntax_Syntax.pos = uu____12115;
                FStar_Syntax_Syntax.vars = uu____12116;_},uu____12117)
               ->
               let env1 =
                 let uu___1709_12159 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1709_12159.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1709_12159.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1709_12159.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1709_12159.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1709_12159.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1709_12159.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1709_12159.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1709_12159.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1709_12159.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1709_12159.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1709_12159.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1709_12159.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1709_12159.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1709_12159.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1709_12159.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1709_12159.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1709_12159.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1709_12159.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1709_12159.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1709_12159.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1709_12159.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1709_12159.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1709_12159.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1709_12159.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1709_12159.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1709_12159.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1709_12159.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1709_12159.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1709_12159.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1709_12159.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1709_12159.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1709_12159.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1709_12159.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1709_12159.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1709_12159.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1709_12159.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1709_12159.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1709_12159.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1709_12159.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1709_12159.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1709_12159.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1709_12159.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12163 =
                 let uu____12166 = bnorm_goal g  in [uu____12166]  in
               add_goals uu____12163
           | uu____12167 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12069
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12229 = if b then t2 else ret false  in
             bind uu____12229 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12255 = trytac comp  in
      bind uu____12255
        (fun uu___4_12267  ->
           match uu___4_12267 with
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
        let uu____12309 =
          bind get
            (fun ps  ->
               let uu____12317 = __tc e t1  in
               bind uu____12317
                 (fun uu____12338  ->
                    match uu____12338 with
                    | (t11,ty1,g1) ->
                        let uu____12351 = __tc e t2  in
                        bind uu____12351
                          (fun uu____12372  ->
                             match uu____12372 with
                             | (t21,ty2,g2) ->
                                 let uu____12385 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12385
                                   (fun uu____12392  ->
                                      let uu____12393 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12393
                                        (fun uu____12401  ->
                                           let uu____12402 =
                                             do_unify e ty1 ty2  in
                                           let uu____12406 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12402 uu____12406)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12309
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12454  ->
             let uu____12455 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12455
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
        (fun uu____12489  ->
           let uu____12490 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12490)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12501 =
      mlog
        (fun uu____12506  ->
           let uu____12507 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12507)
        (fun uu____12512  ->
           let uu____12513 = cur_goal ()  in
           bind uu____12513
             (fun g  ->
                let uu____12519 =
                  let uu____12528 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12528 ty  in
                bind uu____12519
                  (fun uu____12540  ->
                     match uu____12540 with
                     | (ty1,uu____12550,guard) ->
                         let uu____12552 =
                           let uu____12555 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12555 guard  in
                         bind uu____12552
                           (fun uu____12559  ->
                              let uu____12560 =
                                let uu____12564 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12565 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12564 uu____12565 ty1  in
                              bind uu____12560
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12574 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12574
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12581 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12582 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12581
                                          uu____12582
                                         in
                                      let nty =
                                        let uu____12584 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12584 ty1  in
                                      let uu____12585 =
                                        let uu____12589 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12589 ng nty  in
                                      bind uu____12585
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12598 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12598
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12501
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12672 =
      let uu____12681 = cur_goal ()  in
      bind uu____12681
        (fun g  ->
           let uu____12693 =
             let uu____12702 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12702 s_tm  in
           bind uu____12693
             (fun uu____12720  ->
                match uu____12720 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12738 =
                      let uu____12741 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12741 guard  in
                    bind uu____12738
                      (fun uu____12754  ->
                         let uu____12755 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12755 with
                         | (h,args) ->
                             let uu____12800 =
                               let uu____12807 =
                                 let uu____12808 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12808.FStar_Syntax_Syntax.n  in
                               match uu____12807 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12823;
                                      FStar_Syntax_Syntax.vars = uu____12824;_},us)
                                   -> ret (fv, us)
                               | uu____12834 -> fail "type is not an fv"  in
                             bind uu____12800
                               (fun uu____12855  ->
                                  match uu____12855 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12871 =
                                        let uu____12874 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12874 t_lid
                                         in
                                      (match uu____12871 with
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
                                                  (fun uu____12925  ->
                                                     let uu____12926 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12926 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12941 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12969
                                                                  =
                                                                  let uu____12972
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12972
                                                                    c_lid
                                                                   in
                                                                match uu____12969
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
                                                                    uu____13046
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
                                                                    let uu____13051
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13051
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13074
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13074
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13117
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____13117
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____13190
                                                                    =
                                                                    let uu____13192
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____13192
                                                                     in
                                                                    failwhen
                                                                    uu____13190
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13211
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
                                                                    uu___5_13228
                                                                    =
                                                                    match uu___5_13228
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13232)
                                                                    -> true
                                                                    | 
                                                                    uu____13235
                                                                    -> false
                                                                     in
                                                                    let uu____13239
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13239
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
                                                                    uu____13373
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
                                                                    uu____13435
                                                                     ->
                                                                    match uu____13435
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13455),
                                                                    (t,uu____13457))
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
                                                                    uu____13527
                                                                     ->
                                                                    match uu____13527
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13554),
                                                                    (t,uu____13556))
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
                                                                    uu____13615
                                                                     ->
                                                                    match uu____13615
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
                                                                    let uu____13670
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1873_13687
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1873_13687.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13670
                                                                    with
                                                                    | 
                                                                    (uu____13701,uu____13702,uu____13703,pat_t,uu____13705,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13712
                                                                    =
                                                                    let uu____13713
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13713
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13712
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13718
                                                                    =
                                                                    let uu____13727
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13727]
                                                                     in
                                                                    let uu____13746
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13718
                                                                    uu____13746
                                                                     in
                                                                    let nty =
                                                                    let uu____13752
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13752
                                                                     in
                                                                    let uu____13755
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13755
                                                                    (fun
                                                                    uu____13785
                                                                     ->
                                                                    match uu____13785
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
                                                                    let uu____13812
                                                                    =
                                                                    let uu____13823
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13823]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13812
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13859
                                                                    =
                                                                    let uu____13870
                                                                    =
                                                                    let uu____13875
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13875)
                                                                     in
                                                                    (g', br,
                                                                    uu____13870)
                                                                     in
                                                                    ret
                                                                    uu____13859))))))
                                                                    | 
                                                                    uu____13896
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12941
                                                           (fun goal_brs  ->
                                                              let uu____13946
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13946
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
                                                                  let uu____14019
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____14019
                                                                    (
                                                                    fun
                                                                    uu____14030
                                                                     ->
                                                                    let uu____14031
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14031
                                                                    (fun
                                                                    uu____14041
                                                                     ->
                                                                    ret infos))))
                                            | uu____14048 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12672
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14097::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14127 = init xs  in x :: uu____14127
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14140 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14149) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14215 = last args  in
          (match uu____14215 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14245 =
                 let uu____14246 =
                   let uu____14251 =
                     let uu____14252 =
                       let uu____14257 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14257  in
                     uu____14252 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14251, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14246  in
               FStar_All.pipe_left ret uu____14245)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14268,uu____14269) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14322 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14322 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14364 =
                      let uu____14365 =
                        let uu____14370 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14370)  in
                      FStar_Reflection_Data.Tv_Abs uu____14365  in
                    FStar_All.pipe_left ret uu____14364))
      | FStar_Syntax_Syntax.Tm_type uu____14373 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14398 ->
          let uu____14413 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14413 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14444 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14444 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14497 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14510 =
            let uu____14511 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14511  in
          FStar_All.pipe_left ret uu____14510
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14532 =
            let uu____14533 =
              let uu____14538 =
                let uu____14539 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14539  in
              (uu____14538, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14533  in
          FStar_All.pipe_left ret uu____14532
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14579 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14584 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14584 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14637 ->
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
             | FStar_Util.Inr uu____14679 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14683 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14683 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14703 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14709 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14764 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14764
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14785 =
                  let uu____14792 =
                    FStar_List.map
                      (fun uu____14805  ->
                         match uu____14805 with
                         | (p1,uu____14814) -> inspect_pat p1) ps
                     in
                  (fv, uu____14792)  in
                FStar_Reflection_Data.Pat_Cons uu____14785
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
              (fun uu___6_14910  ->
                 match uu___6_14910 with
                 | (pat,uu____14932,t5) ->
                     let uu____14950 = inspect_pat pat  in (uu____14950, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14959 ->
          ((let uu____14961 =
              let uu____14967 =
                let uu____14969 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14971 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14969 uu____14971
                 in
              (FStar_Errors.Warning_CantInspect, uu____14967)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14961);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14140
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14989 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14989
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14993 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14993
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14997 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14997
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15004 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15004
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15029 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15029
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15046 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15046
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15065 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15065
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15069 =
          let uu____15070 =
            let uu____15077 =
              let uu____15078 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15078  in
            FStar_Syntax_Syntax.mk uu____15077  in
          uu____15070 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15069
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15083 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15083
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15094 =
          let uu____15095 =
            let uu____15102 =
              let uu____15103 =
                let uu____15117 =
                  let uu____15120 =
                    let uu____15121 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15121]  in
                  FStar_Syntax_Subst.close uu____15120 t2  in
                ((false, [lb]), uu____15117)  in
              FStar_Syntax_Syntax.Tm_let uu____15103  in
            FStar_Syntax_Syntax.mk uu____15102  in
          uu____15095 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15094
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15163 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15163 with
         | (lbs,body) ->
             let uu____15178 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15178)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15215 =
                let uu____15216 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15216  in
              FStar_All.pipe_left wrap uu____15215
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15223 =
                let uu____15224 =
                  let uu____15238 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15256 = pack_pat p1  in
                         (uu____15256, false)) ps
                     in
                  (fv, uu____15238)  in
                FStar_Syntax_Syntax.Pat_cons uu____15224  in
              FStar_All.pipe_left wrap uu____15223
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
            (fun uu___7_15305  ->
               match uu___7_15305 with
               | (pat,t1) ->
                   let uu____15322 = pack_pat pat  in
                   (uu____15322, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15370 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15370
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15398 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15398
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15444 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15444
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15483 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15483
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15503 =
        bind get
          (fun ps  ->
             let uu____15509 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15509 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15503
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15543 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2171_15550 = ps  in
                 let uu____15551 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2171_15550.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2171_15550.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2171_15550.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2171_15550.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2171_15550.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2171_15550.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2171_15550.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2171_15550.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2171_15550.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2171_15550.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2171_15550.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2171_15550.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15551
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15543
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15578 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15578 with
      | (u,ctx_uvars,g_u) ->
          let uu____15611 = FStar_List.hd ctx_uvars  in
          (match uu____15611 with
           | (ctx_uvar,uu____15625) ->
               let g =
                 let uu____15627 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15627 false
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
        let uu____15650 = goal_of_goal_ty env typ  in
        match uu____15650 with
        | (g,g_u) ->
            let ps =
              let uu____15662 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15665 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15662;
                FStar_Tactics_Types.local_state = uu____15665
              }  in
            let uu____15675 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15675)
  