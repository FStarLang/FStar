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
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
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
           uu____2482 < (Prims.parse_int "5"))
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
             uu____2526 + (Prims.parse_int "1")  in
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
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
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
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___484_3058.FStar_TypeChecker_Env.is_pattern);
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
                      (uu___484_3058.FStar_TypeChecker_Env.nbe)
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
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___505_3194.FStar_TypeChecker_Env.is_pattern);
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
                      (uu___505_3194.FStar_TypeChecker_Env.nbe)
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
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___530_3345.FStar_TypeChecker_Env.is_pattern);
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
                      (uu___530_3345.FStar_TypeChecker_Env.nbe)
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
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___533_3348.FStar_TypeChecker_Env.is_pattern);
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
                      (uu___533_3348.FStar_TypeChecker_Env.nbe)
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
        [FStar_TypeChecker_Env.Eager_unfolding true;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Unmeta;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]  in
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____3458  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___558_3477 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___558_3477.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___558_3477.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___558_3477.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___558_3477.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___558_3477.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___558_3477.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___558_3477.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___558_3477.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___558_3477.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___558_3477.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___558_3477.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___558_3477.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3502 = get_guard_policy ()  in
      bind uu____3502
        (fun old_pol  ->
           let uu____3508 = set_guard_policy pol  in
           bind uu____3508
             (fun uu____3512  ->
                bind t
                  (fun r  ->
                     let uu____3516 = set_guard_policy old_pol  in
                     bind uu____3516 (fun uu____3520  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3524 = let uu____3529 = cur_goal ()  in trytac uu____3529  in
  bind uu____3524
    (fun uu___0_3536  ->
       match uu___0_3536 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3542 = FStar_Options.peek ()  in ret uu____3542)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3567  ->
             let uu____3568 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3568)
          (fun uu____3573  ->
             let uu____3574 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3574
               (fun uu____3578  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3582 =
                         let uu____3583 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3583.FStar_TypeChecker_Env.guard_f  in
                       match uu____3582 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3587 = istrivial e f  in
                           if uu____3587
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3600 =
                                          let uu____3606 =
                                            let uu____3608 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3608
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3606)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3600);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3614  ->
                                           let uu____3615 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3615)
                                        (fun uu____3620  ->
                                           let uu____3621 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3621
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___587_3629 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___587_3629.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___587_3629.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___587_3629.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___587_3629.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3633  ->
                                           let uu____3634 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3634)
                                        (fun uu____3639  ->
                                           let uu____3640 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3640
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___594_3648 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___594_3648.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___594_3648.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___594_3648.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___594_3648.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3652  ->
                                           let uu____3653 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3653)
                                        (fun uu____3657  ->
                                           try
                                             (fun uu___601_3662  ->
                                                match () with
                                                | () ->
                                                    let uu____3665 =
                                                      let uu____3667 =
                                                        let uu____3669 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3669
                                                         in
                                                      Prims.op_Negation
                                                        uu____3667
                                                       in
                                                    if uu____3665
                                                    then
                                                      mlog
                                                        (fun uu____3676  ->
                                                           let uu____3677 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3677)
                                                        (fun uu____3681  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___600_3686 ->
                                               mlog
                                                 (fun uu____3691  ->
                                                    let uu____3692 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3692)
                                                 (fun uu____3696  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____3708 =
      let uu____3711 = cur_goal ()  in
      bind uu____3711
        (fun goal  ->
           let uu____3717 =
             let uu____3726 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3726 t  in
           bind uu____3717
             (fun uu____3738  ->
                match uu____3738 with
                | (uu____3747,lc,uu____3749) ->
                    let uu____3750 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____3750))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____3708
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3766 =
      let uu____3771 = tcc t  in
      bind uu____3771 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3766
  
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
            let uu____3823 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3823 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3835  ->
    let istrivial1 e t =
      let steps =
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Unmeta;
        FStar_TypeChecker_Env.UnfoldTac]  in
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t  in is_true t1
       in
    let uu____3855 = cur_goal ()  in
    bind uu____3855
      (fun goal  ->
         let uu____3861 =
           let uu____3863 = FStar_Tactics_Types.goal_env goal  in
           let uu____3864 = FStar_Tactics_Types.goal_type goal  in
           istrivial1 uu____3863 uu____3864  in
         if uu____3861
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3870 =
              let uu____3872 = FStar_Tactics_Types.goal_env goal  in
              let uu____3873 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3872 uu____3873  in
            fail1 "Not a trivial goal: %s" uu____3870))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3924 =
               try
                 (fun uu___664_3947  ->
                    match () with
                    | () ->
                        let uu____3958 =
                          let uu____3967 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3967
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3958) ()
               with | uu___663_3978 -> fail "divide: not enough goals"  in
             bind uu____3924
               (fun uu____4015  ->
                  match uu____4015 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___646_4041 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___646_4041.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___646_4041.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___646_4041.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___646_4041.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___646_4041.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___646_4041.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___646_4041.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___646_4041.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___646_4041.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___646_4041.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___646_4041.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4042 = set lp  in
                      bind uu____4042
                        (fun uu____4050  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___652_4066 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___652_4066.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___652_4066.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___652_4066.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___652_4066.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___652_4066.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___652_4066.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___652_4066.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___652_4066.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___652_4066.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___652_4066.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___652_4066.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4067 = set rp  in
                                     bind uu____4067
                                       (fun uu____4075  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___658_4091 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___658_4091.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___658_4091.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4092 = set p'
                                                       in
                                                    bind uu____4092
                                                      (fun uu____4100  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4106 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4128 = divide FStar_BigInt.one f idtac  in
    bind uu____4128
      (fun uu____4141  -> match uu____4141 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4179::uu____4180 ->
             let uu____4183 =
               let uu____4192 = map tau  in
               divide FStar_BigInt.one tau uu____4192  in
             bind uu____4183
               (fun uu____4210  ->
                  match uu____4210 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4252 =
        bind t1
          (fun uu____4257  ->
             let uu____4258 = map t2  in
             bind uu____4258 (fun uu____4266  -> ret ()))
         in
      focus uu____4252
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4276  ->
    let uu____4279 =
      let uu____4282 = cur_goal ()  in
      bind uu____4282
        (fun goal  ->
           let uu____4291 =
             let uu____4298 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4298  in
           match uu____4291 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4307 =
                 let uu____4309 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4309  in
               if uu____4307
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4318 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4318 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4334 = new_uvar "intro" env' typ'  in
                  bind uu____4334
                    (fun uu____4351  ->
                       match uu____4351 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4375 = set_solution goal sol  in
                           bind uu____4375
                             (fun uu____4381  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4383 =
                                  let uu____4386 = bnorm_goal g  in
                                  replace_cur uu____4386  in
                                bind uu____4383 (fun uu____4388  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4393 =
                 let uu____4395 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4396 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4395 uu____4396  in
               fail1 "goal is not an arrow (%s)" uu____4393)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4279
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4414  ->
    let uu____4421 = cur_goal ()  in
    bind uu____4421
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4440 =
            let uu____4447 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4447  in
          match uu____4440 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4460 =
                let uu____4462 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4462  in
              if uu____4460
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4479 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4479
                    in
                 let bs =
                   let uu____4490 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4490; b]  in
                 let env' =
                   let uu____4516 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4516 bs  in
                 let uu____4517 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4517
                   (fun uu____4543  ->
                      match uu____4543 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4557 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4560 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4557
                              FStar_Parser_Const.effect_Tot_lid uu____4560 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4578 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4578 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4600 =
                                   let uu____4601 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4601.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4600
                                  in
                               let uu____4617 = set_solution goal tm  in
                               bind uu____4617
                                 (fun uu____4626  ->
                                    let uu____4627 =
                                      let uu____4630 =
                                        bnorm_goal
                                          (let uu___729_4633 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___729_4633.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___729_4633.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___729_4633.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___729_4633.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4630  in
                                    bind uu____4627
                                      (fun uu____4640  ->
                                         let uu____4641 =
                                           let uu____4646 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4646, b)  in
                                         ret uu____4641)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4655 =
                let uu____4657 = FStar_Tactics_Types.goal_env goal  in
                let uu____4658 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4657 uu____4658  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4655))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4678 = cur_goal ()  in
    bind uu____4678
      (fun goal  ->
         mlog
           (fun uu____4685  ->
              let uu____4686 =
                let uu____4688 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4688  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4686)
           (fun uu____4694  ->
              let steps =
                let uu____4698 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4698
                 in
              let t =
                let uu____4702 = FStar_Tactics_Types.goal_env goal  in
                let uu____4703 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4702 uu____4703  in
              let uu____4704 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4704))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4729 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4737 -> g.FStar_Tactics_Types.opts
                 | uu____4740 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4745  ->
                    let uu____4746 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4746)
                 (fun uu____4751  ->
                    let uu____4752 = __tc_lax e t  in
                    bind uu____4752
                      (fun uu____4773  ->
                         match uu____4773 with
                         | (t1,uu____4783,uu____4784) ->
                             let steps =
                               let uu____4788 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4788
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4794  ->
                                  let uu____4795 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4795)
                               (fun uu____4799  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4729
  
let (refine_intro : unit -> unit tac) =
  fun uu____4812  ->
    let uu____4815 =
      let uu____4818 = cur_goal ()  in
      bind uu____4818
        (fun g  ->
           let uu____4825 =
             let uu____4836 = FStar_Tactics_Types.goal_env g  in
             let uu____4837 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4836 uu____4837
              in
           match uu____4825 with
           | (uu____4840,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4866 =
                 let uu____4871 =
                   let uu____4876 =
                     let uu____4877 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4877]  in
                   FStar_Syntax_Subst.open_term uu____4876 phi  in
                 match uu____4871 with
                 | (bvs,phi1) ->
                     let uu____4902 =
                       let uu____4903 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4903  in
                     (uu____4902, phi1)
                  in
               (match uu____4866 with
                | (bv1,phi1) ->
                    let uu____4922 =
                      let uu____4925 = FStar_Tactics_Types.goal_env g  in
                      let uu____4926 =
                        let uu____4927 =
                          let uu____4930 =
                            let uu____4931 =
                              let uu____4938 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4938)  in
                            FStar_Syntax_Syntax.NT uu____4931  in
                          [uu____4930]  in
                        FStar_Syntax_Subst.subst uu____4927 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4925
                        uu____4926 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4922
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4947  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4815
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4970 = cur_goal ()  in
      bind uu____4970
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4979 = FStar_Tactics_Types.goal_env goal  in
               let uu____4980 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4979 uu____4980
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4983 = __tc env t  in
           bind uu____4983
             (fun uu____5002  ->
                match uu____5002 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____5017  ->
                         let uu____5018 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5020 =
                           let uu____5022 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5022
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____5018 uu____5020)
                      (fun uu____5026  ->
                         let uu____5027 =
                           let uu____5030 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5030 guard  in
                         bind uu____5027
                           (fun uu____5033  ->
                              mlog
                                (fun uu____5037  ->
                                   let uu____5038 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5040 =
                                     let uu____5042 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5042
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5038 uu____5040)
                                (fun uu____5046  ->
                                   let uu____5047 =
                                     let uu____5051 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5052 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5051 typ uu____5052  in
                                   bind uu____5047
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____5062 =
                                             let uu____5064 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5064 t1  in
                                           let uu____5065 =
                                             let uu____5067 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____5067 typ  in
                                           let uu____5068 =
                                             let uu____5070 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5071 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____5070 uu____5071  in
                                           let uu____5072 =
                                             let uu____5074 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____5075 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____5074 uu____5075  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____5062 uu____5065 uu____5068
                                             uu____5072)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5101 =
          mlog
            (fun uu____5106  ->
               let uu____5107 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5107)
            (fun uu____5112  ->
               let uu____5113 =
                 let uu____5120 = __exact_now set_expected_typ1 tm  in
                 catch uu____5120  in
               bind uu____5113
                 (fun uu___2_5129  ->
                    match uu___2_5129 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5140  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5144  ->
                             let uu____5145 =
                               let uu____5152 =
                                 let uu____5155 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5155
                                   (fun uu____5160  ->
                                      let uu____5161 = refine_intro ()  in
                                      bind uu____5161
                                        (fun uu____5165  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5152  in
                             bind uu____5145
                               (fun uu___1_5172  ->
                                  match uu___1_5172 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5181  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5184  -> ret ())
                                  | FStar_Util.Inl uu____5185 ->
                                      mlog
                                        (fun uu____5187  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5190  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5101
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5242 = f x  in
          bind uu____5242
            (fun y  ->
               let uu____5250 = mapM f xs  in
               bind uu____5250 (fun ys  -> ret (y :: ys)))
  
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
            let uu____5360 = f e ty2 ty1  in
            bind uu____5360
              (fun uu___3_5374  ->
                 if uu___3_5374
                 then ret acc
                 else
                   (let uu____5394 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5394 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5415 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5417 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5415
                          uu____5417
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5434 =
                          let uu____5436 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5436  in
                        if uu____5434
                        then fail "Codomain is effectful"
                        else
                          (let uu____5460 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5460
                             (fun uu____5487  ->
                                match uu____5487 with
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
        let uu____5593 =
          mlog
            (fun uu____5598  ->
               let uu____5599 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5599)
            (fun uu____5604  ->
               let uu____5605 = cur_goal ()  in
               bind uu____5605
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5613 = __tc e tm  in
                    bind uu____5613
                      (fun uu____5634  ->
                         match uu____5634 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5647 =
                               let uu____5658 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5658
                                in
                             bind uu____5647
                               (fun uvs  ->
                                  let fix_qual q =
                                    match q with
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Meta uu____5696)
                                        ->
                                        FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit false)
                                    | uu____5700 -> q  in
                                  let w =
                                    FStar_List.fold_right
                                      (fun uu____5723  ->
                                         fun w  ->
                                           match uu____5723 with
                                           | (uvt,q,uu____5741) ->
                                               FStar_Syntax_Util.mk_app w
                                                 [(uvt, (fix_qual q))]) uvs
                                      tm1
                                     in
                                  let uvset =
                                    let uu____5773 =
                                      FStar_Syntax_Free.new_uv_set ()  in
                                    FStar_List.fold_right
                                      (fun uu____5790  ->
                                         fun s  ->
                                           match uu____5790 with
                                           | (uu____5802,uu____5803,uv) ->
                                               let uu____5805 =
                                                 FStar_Syntax_Free.uvars
                                                   uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                  in
                                               FStar_Util.set_union s
                                                 uu____5805) uvs uu____5773
                                     in
                                  let free_in_some_goal uv =
                                    FStar_Util.set_mem uv uvset  in
                                  let uu____5815 = solve' goal w  in
                                  bind uu____5815
                                    (fun uu____5820  ->
                                       let uu____5821 =
                                         mapM
                                           (fun uu____5838  ->
                                              match uu____5838 with
                                              | (uvt,q,uv) ->
                                                  let uu____5850 =
                                                    FStar_Syntax_Unionfind.find
                                                      uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                     in
                                                  (match uu____5850 with
                                                   | FStar_Pervasives_Native.Some
                                                       uu____5855 -> 
                                                       ret ()
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       let uu____5856 =
                                                         uopt &&
                                                           (free_in_some_goal
                                                              uv)
                                                          in
                                                       if uu____5856
                                                       then ret ()
                                                       else
                                                         (let uu____5863 =
                                                            let uu____5866 =
                                                              bnorm_goal
                                                                (let uu___895_5869
                                                                   = goal  in
                                                                 {
                                                                   FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___895_5869.FStar_Tactics_Types.goal_main_env);
                                                                   FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                   FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___895_5869.FStar_Tactics_Types.opts);
                                                                   FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                   FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___895_5869.FStar_Tactics_Types.label)
                                                                 })
                                                               in
                                                            [uu____5866]  in
                                                          add_goals
                                                            uu____5863))) uvs
                                          in
                                       bind uu____5821
                                         (fun uu____5874  ->
                                            proc_guard "apply guard" e guard))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5593
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5902 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5902
    then
      let uu____5911 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5926 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5979 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5911 with
      | (pre,post) ->
          let post1 =
            let uu____6012 =
              let uu____6023 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6023]  in
            FStar_Syntax_Util.mk_app post uu____6012  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6054 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6054
       then
         let uu____6063 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6063
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
            let uu____6142 = f x e  in
            bind uu____6142 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6157 =
      let uu____6160 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6167  ->
                  let uu____6168 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6168)
               (fun uu____6174  ->
                  let is_unit_t t =
                    let uu____6182 =
                      let uu____6183 = FStar_Syntax_Subst.compress t  in
                      uu____6183.FStar_Syntax_Syntax.n  in
                    match uu____6182 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6189 -> false  in
                  let uu____6191 = cur_goal ()  in
                  bind uu____6191
                    (fun goal  ->
                       mlog
                         (fun uu____6198  ->
                            let uu____6199 = goal_to_string_verbose goal  in
                            FStar_Util.print1 "apply_lemma: goal = %s\n"
                              uu____6199)
                         (fun uu____6204  ->
                            let uu____6205 =
                              let uu____6214 =
                                FStar_Tactics_Types.goal_env goal  in
                              __tc uu____6214 tm  in
                            bind uu____6205
                              (fun uu____6225  ->
                                 match uu____6225 with
                                 | (tm1,t,guard) ->
                                     mlog
                                       (fun uu____6240  ->
                                          let uu____6241 =
                                            FStar_Syntax_Print.term_to_string
                                              tm1
                                             in
                                          let uu____6243 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          FStar_Util.print2
                                            "apply_lemma: tc_goal = %s, %s\n"
                                            uu____6241 uu____6243)
                                       (fun uu____6251  ->
                                          let uu____6252 =
                                            FStar_Syntax_Util.arrow_formals_comp
                                              t
                                             in
                                          match uu____6252 with
                                          | (bs,comp) ->
                                              let uu____6285 =
                                                lemma_or_sq comp  in
                                              (match uu____6285 with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   fail
                                                     "not a lemma or squashed function"
                                               | FStar_Pervasives_Native.Some
                                                   (pre,post) ->
                                                   let uu____6305 =
                                                     fold_left
                                                       (fun uu____6367  ->
                                                          fun uu____6368  ->
                                                            match (uu____6367,
                                                                    uu____6368)
                                                            with
                                                            | ((b,aq),
                                                               (uvs,imps,subst1))
                                                                ->
                                                                let b_t =
                                                                  FStar_Syntax_Subst.subst
                                                                    subst1
                                                                    b.FStar_Syntax_Syntax.sort
                                                                   in
                                                                let uu____6519
                                                                  =
                                                                  is_unit_t
                                                                    b_t
                                                                   in
                                                                if uu____6519
                                                                then
                                                                  FStar_All.pipe_left
                                                                    ret
                                                                    (((FStar_Syntax_Util.exp_unit,
                                                                    aq) ::
                                                                    uvs),
                                                                    imps,
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                    ::
                                                                    subst1))
                                                                else
                                                                  (let uu____6642
                                                                    =
                                                                    let uu____6649
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    new_uvar
                                                                    "apply_lemma"
                                                                    uu____6649
                                                                    b_t  in
                                                                   bind
                                                                    uu____6642
                                                                    (fun
                                                                    uu____6680
                                                                     ->
                                                                    match uu____6680
                                                                    with
                                                                    | 
                                                                    (t1,u) ->
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
                                                   bind uu____6305
                                                     (fun uu____6861  ->
                                                        match uu____6861 with
                                                        | (uvs,implicits,subst1)
                                                            ->
                                                            mlog
                                                              (fun uu____6923
                                                                  ->
                                                                 let uu____6924
                                                                   =
                                                                   FStar_Syntax_Print.subst_to_string
                                                                    subst1
                                                                    in
                                                                 FStar_Util.print1
                                                                   "apply_lemma: subst = %s"
                                                                   uu____6924)
                                                              (fun uu____6933
                                                                  ->
                                                                 let implicits1
                                                                   =
                                                                   FStar_List.rev
                                                                    implicits
                                                                    in
                                                                 let uvs1 =
                                                                   FStar_List.rev
                                                                    uvs
                                                                    in
                                                                 let pre1 =
                                                                   FStar_Syntax_Subst.subst
                                                                    subst1
                                                                    pre
                                                                    in
                                                                 let post1 =
                                                                   FStar_Syntax_Subst.subst
                                                                    subst1
                                                                    post
                                                                    in
                                                                 let uu____6962
                                                                   =
                                                                   let uu____6966
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   let uu____6967
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    post1  in
                                                                   let uu____6968
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal  in
                                                                   do_unify
                                                                    uu____6966
                                                                    uu____6967
                                                                    uu____6968
                                                                    in
                                                                 bind
                                                                   uu____6962
                                                                   (fun b  ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    b
                                                                    then
                                                                    let uu____6979
                                                                    =
                                                                    let uu____6981
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    tts
                                                                    uu____6981
                                                                    tm1  in
                                                                    let uu____6982
                                                                    =
                                                                    let uu____6984
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6985
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    post1  in
                                                                    tts
                                                                    uu____6984
                                                                    uu____6985
                                                                     in
                                                                    let uu____6986
                                                                    =
                                                                    let uu____6988
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6989
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal  in
                                                                    tts
                                                                    uu____6988
                                                                    uu____6989
                                                                     in
                                                                    fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu____6979
                                                                    uu____6982
                                                                    uu____6986
                                                                    else
                                                                    (let uu____6993
                                                                    =
                                                                    solve'
                                                                    goal
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    bind
                                                                    uu____6993
                                                                    (fun
                                                                    uu____7001
                                                                     ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu____7027
                                                                    =
                                                                    let uu____7030
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____7030
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____7027
                                                                     in
                                                                    FStar_List.existsML
                                                                    (fun u 
                                                                    ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                     in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_List.existsML
                                                                    (fun g' 
                                                                    ->
                                                                    let uu____7066
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____7066)
                                                                    goals  in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu____7083
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                    match uu____7083
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7102)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____7129)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7146
                                                                    -> false)
                                                                     in
                                                                    let uu____7148
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    implicits1
                                                                    (mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let t1 =
                                                                    FStar_Util.now
                                                                    ()  in
                                                                    let uu____7191
                                                                    = imp  in
                                                                    match uu____7191
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7202
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7202
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7224)
                                                                    ->
                                                                    let uu____7249
                                                                    =
                                                                    let uu____7250
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7250.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7249
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7258)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1010_7278
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1010_7278.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1010_7278.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1010_7278.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1010_7278.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7281
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7287
                                                                     ->
                                                                    let uu____7288
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7290
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7288
                                                                    uu____7290)
                                                                    (fun
                                                                    uu____7297
                                                                     ->
                                                                    let env =
                                                                    let uu___1015_7299
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1015_7299.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7302
                                                                    =
                                                                    let uu____7305
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7309
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7311
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7309
                                                                    uu____7311
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7317
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7305
                                                                    uu____7317
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7302
                                                                    (fun
                                                                    uu____7321
                                                                     ->
                                                                    ret []))))))
                                                                     in
                                                                    bind
                                                                    uu____7148
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
                                                                    let uu____7385
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7385
                                                                    then
                                                                    let uu____7390
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7390
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
                                                                    let uu____7405
                                                                    =
                                                                    let uu____7407
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7407
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7405)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7408
                                                                    =
                                                                    let uu____7411
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7411
                                                                    guard  in
                                                                    bind
                                                                    uu____7408
                                                                    (fun
                                                                    uu____7414
                                                                     ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7417
                                                                     ->
                                                                    let uu____7418
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    pre1  in
                                                                    FStar_Util.print1
                                                                    ">>>apply_lemma proc_guard done ... guard = %s\n"
                                                                    uu____7418)
                                                                    (fun
                                                                    uu____7423
                                                                     ->
                                                                    let uu____7424
                                                                    =
                                                                    let uu____7427
                                                                    =
                                                                    let uu____7429
                                                                    =
                                                                    let uu____7431
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7432
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7431
                                                                    uu____7432
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7429
                                                                     in
                                                                    if
                                                                    uu____7427
                                                                    then
                                                                    let uu____7436
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7436
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7424
                                                                    (fun
                                                                    uu____7441
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))))
         in
      focus uu____6160  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6157
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7465 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7465 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7475::(e1,uu____7477)::(e2,uu____7479)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____7540 ->
        let uu____7543 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7543 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____7558 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____7558);
              (let uu____7561 = FStar_Syntax_Util.head_and_args t  in
               match uu____7561 with
               | (hd1,args) ->
                   let uu____7610 =
                     let uu____7625 =
                       let uu____7626 = FStar_Syntax_Subst.compress hd1  in
                       uu____7626.FStar_Syntax_Syntax.n  in
                     (uu____7625, args)  in
                   (match uu____7610 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____7646,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____7647))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____7712 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____7714 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____7712
                            uu____7714);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____7721 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7758 = destruct_eq' typ  in
    match uu____7758 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7788 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7788 with
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
        let uu____7857 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7857 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7915 = aux e'  in
               FStar_Util.map_opt uu____7915
                 (fun uu____7946  ->
                    match uu____7946 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7972 = aux e  in
      FStar_Util.map_opt uu____7972
        (fun uu____8003  ->
           match uu____8003 with
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
          let uu____8077 =
            let uu____8088 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8088  in
          FStar_Util.map_opt uu____8077
            (fun uu____8106  ->
               match uu____8106 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1115_8128 = bv  in
                     let uu____8129 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1115_8128.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1115_8128.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____8129
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1119_8137 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____8138 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____8147 =
                       let uu____8150 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____8150  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1119_8137.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____8138;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____8147;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1119_8137.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1119_8137.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1119_8137.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1119_8137.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1122_8151 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1122_8151.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1122_8151.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1122_8151.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1122_8151.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8162 =
      let uu____8165 = cur_goal ()  in
      bind uu____8165
        (fun goal  ->
           let uu____8173 = h  in
           match uu____8173 with
           | (bv,uu____8177) ->
               mlog
                 (fun uu____8185  ->
                    let uu____8186 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8188 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8186
                      uu____8188)
                 (fun uu____8193  ->
                    let uu____8194 =
                      let uu____8205 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8205  in
                    match uu____8194 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8232 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8232 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8247 =
                               let uu____8248 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8248.FStar_Syntax_Syntax.n  in
                             (match uu____8247 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1145_8265 = bv2  in
                                    let uu____8266 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1145_8265.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1145_8265.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8266
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1149_8274 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8275 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8284 =
                                      let uu____8287 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8287
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1149_8274.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8275;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8284;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1149_8274.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1149_8274.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1149_8274.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1149_8274.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1152_8290 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1152_8290.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1152_8290.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1152_8290.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1152_8290.FStar_Tactics_Types.label)
                                     })
                              | uu____8291 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8293 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8162
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____8323 =
        let uu____8326 = cur_goal ()  in
        bind uu____8326
          (fun goal  ->
             let uu____8337 = b  in
             match uu____8337 with
             | (bv,uu____8341) ->
                 let bv' =
                   let uu____8347 =
                     let uu___1163_8348 = bv  in
                     let uu____8349 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8349;
                       FStar_Syntax_Syntax.index =
                         (uu___1163_8348.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1163_8348.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8347  in
                 let s1 =
                   let uu____8354 =
                     let uu____8355 =
                       let uu____8362 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8362)  in
                     FStar_Syntax_Syntax.NT uu____8355  in
                   [uu____8354]  in
                 let uu____8367 = subst_goal bv bv' s1 goal  in
                 (match uu____8367 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8323
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
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
                    let uu____8448 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8448 with
                     | (ty,u) ->
                         let uu____8457 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8457
                           (fun uu____8476  ->
                              match uu____8476 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1187_8486 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1187_8486.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1187_8486.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8490 =
                                      let uu____8491 =
                                        let uu____8498 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8498)  in
                                      FStar_Syntax_Syntax.NT uu____8491  in
                                    [uu____8490]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1192_8510 = b1  in
                                         let uu____8511 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1192_8510.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1192_8510.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8511
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8518  ->
                                       let new_goal =
                                         let uu____8520 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8521 =
                                           let uu____8522 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8522
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8520 uu____8521
                                          in
                                       let uu____8523 = add_goals [new_goal]
                                          in
                                       bind uu____8523
                                         (fun uu____8528  ->
                                            let uu____8529 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8529
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8389
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8555 =
        let uu____8558 = cur_goal ()  in
        bind uu____8558
          (fun goal  ->
             let uu____8567 = b  in
             match uu____8567 with
             | (bv,uu____8571) ->
                 let uu____8576 =
                   let uu____8587 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8587  in
                 (match uu____8576 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8617 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8617
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1213_8622 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1213_8622.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1213_8622.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8624 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8624))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8555
  
let (revert : unit -> unit tac) =
  fun uu____8637  ->
    let uu____8640 = cur_goal ()  in
    bind uu____8640
      (fun goal  ->
         let uu____8646 =
           let uu____8653 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8653  in
         match uu____8646 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8670 =
                 let uu____8673 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8673  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8670
                in
             let uu____8688 = new_uvar "revert" env' typ'  in
             bind uu____8688
               (fun uu____8704  ->
                  match uu____8704 with
                  | (r,u_r) ->
                      let uu____8713 =
                        let uu____8716 =
                          let uu____8717 =
                            let uu____8718 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8718.FStar_Syntax_Syntax.pos  in
                          let uu____8721 =
                            let uu____8726 =
                              let uu____8727 =
                                let uu____8736 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8736  in
                              [uu____8727]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8726  in
                          uu____8721 FStar_Pervasives_Native.None uu____8717
                           in
                        set_solution goal uu____8716  in
                      bind uu____8713
                        (fun uu____8755  ->
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
      let uu____8769 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8769
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8785 = cur_goal ()  in
    bind uu____8785
      (fun goal  ->
         mlog
           (fun uu____8793  ->
              let uu____8794 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8796 =
                let uu____8798 =
                  let uu____8800 =
                    let uu____8809 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8809  in
                  FStar_All.pipe_right uu____8800 FStar_List.length  in
                FStar_All.pipe_right uu____8798 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8794 uu____8796)
           (fun uu____8830  ->
              let uu____8831 =
                let uu____8842 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8842  in
              match uu____8831 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8887 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8887
                        then
                          let uu____8892 =
                            let uu____8894 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8894
                             in
                          fail uu____8892
                        else check1 bvs2
                     in
                  let uu____8899 =
                    let uu____8901 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8901  in
                  if uu____8899
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8908 = check1 bvs  in
                     bind uu____8908
                       (fun uu____8914  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8916 =
                            let uu____8923 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8923  in
                          bind uu____8916
                            (fun uu____8933  ->
                               match uu____8933 with
                               | (ut,uvar_ut) ->
                                   let uu____8942 = set_solution goal ut  in
                                   bind uu____8942
                                     (fun uu____8947  ->
                                        let uu____8948 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8948))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8956  ->
    let uu____8959 = cur_goal ()  in
    bind uu____8959
      (fun goal  ->
         let uu____8965 =
           let uu____8972 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8972  in
         match uu____8965 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8981) ->
             let uu____8986 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8986)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8999 = cur_goal ()  in
    bind uu____8999
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9009 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9009  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9012  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9025 = cur_goal ()  in
    bind uu____9025
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9035 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9035  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9038  -> add_goals [g']))
  
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
            let uu____9079 = FStar_Syntax_Subst.compress t  in
            uu____9079.FStar_Syntax_Syntax.n  in
          let uu____9082 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1397_9089 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1397_9089.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1397_9089.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9082
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9106 =
                   let uu____9107 = FStar_Syntax_Subst.compress t1  in
                   uu____9107.FStar_Syntax_Syntax.n  in
                 match uu____9106 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9138 = ff hd1  in
                     bind uu____9138
                       (fun hd2  ->
                          let fa uu____9164 =
                            match uu____9164 with
                            | (a,q) ->
                                let uu____9185 = ff a  in
                                bind uu____9185 (fun a1  -> ret (a1, q))
                             in
                          let uu____9204 = mapM fa args  in
                          bind uu____9204
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9286 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9286 with
                      | (bs1,t') ->
                          let uu____9295 =
                            let uu____9298 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9298 t'  in
                          bind uu____9295
                            (fun t''  ->
                               let uu____9302 =
                                 let uu____9303 =
                                   let uu____9322 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9331 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9322, uu____9331, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9303  in
                               ret uu____9302))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9406 = ff hd1  in
                     bind uu____9406
                       (fun hd2  ->
                          let ffb br =
                            let uu____9421 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9421 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9453 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9453  in
                                let uu____9454 = ff1 e  in
                                bind uu____9454
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9469 = mapM ffb brs  in
                          bind uu____9469
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9513;
                          FStar_Syntax_Syntax.lbtyp = uu____9514;
                          FStar_Syntax_Syntax.lbeff = uu____9515;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9517;
                          FStar_Syntax_Syntax.lbpos = uu____9518;_}::[]),e)
                     ->
                     let lb =
                       let uu____9546 =
                         let uu____9547 = FStar_Syntax_Subst.compress t1  in
                         uu____9547.FStar_Syntax_Syntax.n  in
                       match uu____9546 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9551) -> lb
                       | uu____9567 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9577 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9577
                         (fun def1  ->
                            ret
                              (let uu___1350_9583 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1350_9583.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1350_9583.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1350_9583.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1350_9583.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1350_9583.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1350_9583.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9584 = fflb lb  in
                     bind uu____9584
                       (fun lb1  ->
                          let uu____9594 =
                            let uu____9599 =
                              let uu____9600 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9600]  in
                            FStar_Syntax_Subst.open_term uu____9599 e  in
                          match uu____9594 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9630 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9630  in
                              let uu____9631 = ff1 e1  in
                              bind uu____9631
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9678 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9678
                         (fun def  ->
                            ret
                              (let uu___1368_9684 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1368_9684.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1368_9684.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1368_9684.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1368_9684.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1368_9684.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1368_9684.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9685 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9685 with
                      | (lbs1,e1) ->
                          let uu____9700 = mapM fflb lbs1  in
                          bind uu____9700
                            (fun lbs2  ->
                               let uu____9712 = ff e1  in
                               bind uu____9712
                                 (fun e2  ->
                                    let uu____9720 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9720 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9791 = ff t2  in
                     bind uu____9791
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9822 = ff t2  in
                     bind uu____9822
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9829 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1392_9836 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1392_9836.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1392_9836.FStar_Syntax_Syntax.vars)
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
              let uu____9883 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1405_9892 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1405_9892.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1405_9892.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1405_9892.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1405_9892.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1405_9892.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1405_9892.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1405_9892.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1405_9892.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1405_9892.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1405_9892.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1405_9892.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1405_9892.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1405_9892.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1405_9892.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1405_9892.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1405_9892.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1405_9892.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1405_9892.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1405_9892.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1405_9892.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1405_9892.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1405_9892.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1405_9892.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1405_9892.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1405_9892.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1405_9892.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1405_9892.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1405_9892.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1405_9892.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1405_9892.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1405_9892.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1405_9892.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1405_9892.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1405_9892.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1405_9892.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1405_9892.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1405_9892.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1405_9892.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1405_9892.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1405_9892.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1405_9892.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1405_9892.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9883 with
              | (t1,lcomp,g) ->
                  let uu____9899 =
                    (let uu____9903 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9903) ||
                      (let uu____9906 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9906)
                     in
                  if uu____9899
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9917 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9917
                         (fun uu____9934  ->
                            match uu____9934 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9947  ->
                                      let uu____9948 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9950 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9948 uu____9950);
                                 (let uu____9953 =
                                    let uu____9956 =
                                      let uu____9957 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9957 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9956
                                      opts label1
                                     in
                                  bind uu____9953
                                    (fun uu____9961  ->
                                       let uu____9962 =
                                         bind tau
                                           (fun uu____9968  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9974  ->
                                                   let uu____9975 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9977 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9975 uu____9977);
                                              ret ut1)
                                          in
                                       focus uu____9962))))
                        in
                     let uu____9980 = catch rewrite_eq  in
                     bind uu____9980
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
          let uu____10192 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10192
            (fun t1  ->
               let uu____10200 =
                 f env
                   (let uu___1482_10208 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1482_10208.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1482_10208.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10200
                 (fun uu____10224  ->
                    match uu____10224 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10247 =
                               let uu____10248 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10248.FStar_Syntax_Syntax.n  in
                             match uu____10247 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10285 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10285
                                   (fun uu____10307  ->
                                      match uu____10307 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10323 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10323
                                            (fun uu____10347  ->
                                               match uu____10347 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1462_10377 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1462_10377.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1462_10377.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10419 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10419 with
                                  | (bs1,t') ->
                                      let uu____10434 =
                                        let uu____10441 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10441 ctrl1 t'
                                         in
                                      bind uu____10434
                                        (fun uu____10456  ->
                                           match uu____10456 with
                                           | (t'',ctrl2) ->
                                               let uu____10471 =
                                                 let uu____10478 =
                                                   let uu___1475_10481 = t4
                                                      in
                                                   let uu____10484 =
                                                     let uu____10485 =
                                                       let uu____10504 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10513 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10504,
                                                         uu____10513, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10485
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10484;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1475_10481.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1475_10481.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10478, ctrl2)  in
                                               ret uu____10471))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10566 -> ret (t3, ctrl1))))

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
              let uu____10612 = ctrl_tac_fold f env ctrl t  in
              bind uu____10612
                (fun uu____10633  ->
                   match uu____10633 with
                   | (t1,ctrl1) ->
                       let uu____10648 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10648
                         (fun uu____10672  ->
                            match uu____10672 with
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
                let uu____10763 =
                  let uu____10771 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10771
                    (fun uu____10782  ->
                       let uu____10783 = ctrl t1  in
                       bind uu____10783
                         (fun res  ->
                            let uu____10809 = trivial ()  in
                            bind uu____10809 (fun uu____10818  -> ret res)))
                   in
                bind uu____10763
                  (fun uu____10836  ->
                     match uu____10836 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10865 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1512_10874 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1512_10874.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1512_10874.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1512_10874.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1512_10874.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1512_10874.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1512_10874.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1512_10874.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1512_10874.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1512_10874.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1512_10874.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1512_10874.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1512_10874.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1512_10874.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1512_10874.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1512_10874.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1512_10874.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1512_10874.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1512_10874.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1512_10874.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1512_10874.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1512_10874.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1512_10874.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1512_10874.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1512_10874.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1512_10874.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1512_10874.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1512_10874.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1512_10874.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1512_10874.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1512_10874.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1512_10874.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1512_10874.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1512_10874.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1512_10874.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1512_10874.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1512_10874.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1512_10874.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1512_10874.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1512_10874.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1512_10874.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1512_10874.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1512_10874.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10865 with
                            | (t2,lcomp,g) ->
                                let uu____10885 =
                                  (let uu____10889 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10889) ||
                                    (let uu____10892 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10892)
                                   in
                                if uu____10885
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10908 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10908
                                     (fun uu____10929  ->
                                        match uu____10929 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10946  ->
                                                  let uu____10947 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10949 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10947 uu____10949);
                                             (let uu____10952 =
                                                let uu____10955 =
                                                  let uu____10956 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10956 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10955 opts label1
                                                 in
                                              bind uu____10952
                                                (fun uu____10964  ->
                                                   let uu____10965 =
                                                     bind rewriter
                                                       (fun uu____10979  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10985 
                                                               ->
                                                               let uu____10986
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10988
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10986
                                                                 uu____10988);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10965)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____11033 =
        bind get
          (fun ps  ->
             let uu____11043 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11043 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11081  ->
                       let uu____11082 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11082);
                  bind dismiss_all
                    (fun uu____11087  ->
                       let uu____11088 =
                         let uu____11095 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11095
                           keepGoing gt1
                          in
                       bind uu____11088
                         (fun uu____11105  ->
                            match uu____11105 with
                            | (gt',uu____11113) ->
                                (log ps
                                   (fun uu____11117  ->
                                      let uu____11118 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____11118);
                                 (let uu____11121 = push_goals gs  in
                                  bind uu____11121
                                    (fun uu____11126  ->
                                       let uu____11127 =
                                         let uu____11130 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____11130]  in
                                       add_goals uu____11127)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11033
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11155 =
        bind get
          (fun ps  ->
             let uu____11165 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11165 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11203  ->
                       let uu____11204 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11204);
                  bind dismiss_all
                    (fun uu____11209  ->
                       let uu____11210 =
                         let uu____11213 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11213 gt1
                          in
                       bind uu____11210
                         (fun gt'  ->
                            log ps
                              (fun uu____11221  ->
                                 let uu____11222 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11222);
                            (let uu____11225 = push_goals gs  in
                             bind uu____11225
                               (fun uu____11230  ->
                                  let uu____11231 =
                                    let uu____11234 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11234]  in
                                  add_goals uu____11231))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____11155
  
let (trefl : unit -> unit tac) =
  fun uu____11247  ->
    let uu____11250 =
      let uu____11253 = cur_goal ()  in
      bind uu____11253
        (fun g  ->
           let uu____11271 =
             let uu____11276 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____11276  in
           match uu____11271 with
           | FStar_Pervasives_Native.Some t ->
               let uu____11284 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____11284 with
                | (hd1,args) ->
                    let uu____11323 =
                      let uu____11336 =
                        let uu____11337 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____11337.FStar_Syntax_Syntax.n  in
                      (uu____11336, args)  in
                    (match uu____11323 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____11351::(l,uu____11353)::(r,uu____11355)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____11402 =
                           let uu____11406 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____11406 l r  in
                         bind uu____11402
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____11417 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11417 l
                                    in
                                 let r1 =
                                   let uu____11419 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11419 r
                                    in
                                 let uu____11420 =
                                   let uu____11424 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____11424 l1 r1  in
                                 bind uu____11420
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____11434 =
                                           let uu____11436 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11436 l1  in
                                         let uu____11437 =
                                           let uu____11439 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11439 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____11434 uu____11437))))
                     | (hd2,uu____11442) ->
                         let uu____11459 =
                           let uu____11461 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____11461 t  in
                         fail1 "trefl: not an equality (%s)" uu____11459))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11250
  
let (dup : unit -> unit tac) =
  fun uu____11478  ->
    let uu____11481 = cur_goal ()  in
    bind uu____11481
      (fun g  ->
         let uu____11487 =
           let uu____11494 = FStar_Tactics_Types.goal_env g  in
           let uu____11495 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11494 uu____11495  in
         bind uu____11487
           (fun uu____11505  ->
              match uu____11505 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1604_11515 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1604_11515.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1604_11515.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1604_11515.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1604_11515.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11518  ->
                       let uu____11519 =
                         let uu____11522 = FStar_Tactics_Types.goal_env g  in
                         let uu____11523 =
                           let uu____11524 =
                             let uu____11525 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11526 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11525
                               uu____11526
                              in
                           let uu____11527 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11528 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11524 uu____11527 u
                             uu____11528
                            in
                         add_irrelevant_goal "dup equation" uu____11522
                           uu____11523 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11519
                         (fun uu____11532  ->
                            let uu____11533 = add_goals [g']  in
                            bind uu____11533 (fun uu____11537  -> ret ())))))
  
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
              let uu____11663 = f x y  in
              if uu____11663 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11686 -> (acc, l11, l21)  in
        let uu____11701 = aux [] l1 l2  in
        match uu____11701 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11807 = get_phi g1  in
      match uu____11807 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11814 = get_phi g2  in
          (match uu____11814 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11827 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11827 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11858 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11858 phi1  in
                    let t2 =
                      let uu____11868 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11868 phi2  in
                    let uu____11877 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11877
                      (fun uu____11882  ->
                         let uu____11883 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11883
                           (fun uu____11890  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1655_11895 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11896 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1655_11895.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1655_11895.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1655_11895.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1655_11895.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11896;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1655_11895.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1655_11895.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1655_11895.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1655_11895.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1655_11895.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1655_11895.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1655_11895.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1655_11895.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1655_11895.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1655_11895.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1655_11895.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1655_11895.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1655_11895.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1655_11895.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1655_11895.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1655_11895.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1655_11895.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1655_11895.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1655_11895.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1655_11895.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1655_11895.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1655_11895.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1655_11895.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1655_11895.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1655_11895.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1655_11895.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1655_11895.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1655_11895.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1655_11895.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1655_11895.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1655_11895.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1655_11895.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1655_11895.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1655_11895.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1655_11895.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1655_11895.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1655_11895.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11900 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11900
                                (fun goal  ->
                                   mlog
                                     (fun uu____11910  ->
                                        let uu____11911 =
                                          goal_to_string_verbose g1  in
                                        let uu____11913 =
                                          goal_to_string_verbose g2  in
                                        let uu____11915 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11911 uu____11913 uu____11915)
                                     (fun uu____11919  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11927  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11943 =
               set
                 (let uu___1670_11948 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1670_11948.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1670_11948.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1670_11948.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1670_11948.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1670_11948.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1670_11948.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1670_11948.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1670_11948.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1670_11948.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1670_11948.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1670_11948.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1670_11948.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11943
               (fun uu____11951  ->
                  let uu____11952 = join_goals g1 g2  in
                  bind uu____11952 (fun g12  -> add_goals [g12]))
         | uu____11957 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11973 =
      let uu____11976 = cur_goal ()  in
      bind uu____11976
        (fun g  ->
           FStar_Options.push ();
           (let uu____11989 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11989);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1681_11996 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1681_11996.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1681_11996.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1681_11996.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1681_11996.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11973
  
let (top_env : unit -> env tac) =
  fun uu____12013  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____12028  ->
    let uu____12032 = cur_goal ()  in
    bind uu____12032
      (fun g  ->
         let uu____12039 =
           (FStar_Options.lax ()) ||
             (let uu____12042 = FStar_Tactics_Types.goal_env g  in
              uu____12042.FStar_TypeChecker_Env.lax)
            in
         ret uu____12039)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____12059 =
        mlog
          (fun uu____12064  ->
             let uu____12065 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____12065)
          (fun uu____12070  ->
             let uu____12071 = cur_goal ()  in
             bind uu____12071
               (fun goal  ->
                  let env =
                    let uu____12079 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12079 ty  in
                  let uu____12080 = __tc_ghost env tm  in
                  bind uu____12080
                    (fun uu____12099  ->
                       match uu____12099 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12113  ->
                                let uu____12114 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12114)
                             (fun uu____12118  ->
                                mlog
                                  (fun uu____12121  ->
                                     let uu____12122 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12122)
                                  (fun uu____12127  ->
                                     let uu____12128 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12128
                                       (fun uu____12133  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____12059
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12158 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12164 =
              let uu____12171 =
                let uu____12172 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12172
                 in
              new_uvar "uvar_env.2" env uu____12171  in
            bind uu____12164
              (fun uu____12189  ->
                 match uu____12189 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12158
        (fun typ  ->
           let uu____12201 = new_uvar "uvar_env" env typ  in
           bind uu____12201
             (fun uu____12216  ->
                match uu____12216 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12235 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12254 -> g.FStar_Tactics_Types.opts
             | uu____12257 -> FStar_Options.peek ()  in
           let uu____12260 = FStar_Syntax_Util.head_and_args t  in
           match uu____12260 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12280);
                FStar_Syntax_Syntax.pos = uu____12281;
                FStar_Syntax_Syntax.vars = uu____12282;_},uu____12283)
               ->
               let env1 =
                 let uu___1735_12325 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1735_12325.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1735_12325.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1735_12325.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1735_12325.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1735_12325.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1735_12325.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1735_12325.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1735_12325.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1735_12325.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1735_12325.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1735_12325.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1735_12325.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1735_12325.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1735_12325.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1735_12325.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1735_12325.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1735_12325.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1735_12325.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1735_12325.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1735_12325.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1735_12325.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1735_12325.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1735_12325.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1735_12325.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1735_12325.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1735_12325.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1735_12325.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1735_12325.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1735_12325.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1735_12325.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1735_12325.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1735_12325.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1735_12325.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1735_12325.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1735_12325.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1735_12325.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1735_12325.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1735_12325.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1735_12325.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1735_12325.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1735_12325.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1735_12325.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12329 =
                 let uu____12332 = bnorm_goal g  in [uu____12332]  in
               add_goals uu____12329
           | uu____12333 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12235
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12395 = if b then t2 else ret false  in
             bind uu____12395 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12421 = trytac comp  in
      bind uu____12421
        (fun uu___4_12433  ->
           match uu___4_12433 with
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
        let uu____12475 =
          bind get
            (fun ps  ->
               let uu____12483 = __tc e t1  in
               bind uu____12483
                 (fun uu____12504  ->
                    match uu____12504 with
                    | (t11,ty1,g1) ->
                        let uu____12517 = __tc e t2  in
                        bind uu____12517
                          (fun uu____12538  ->
                             match uu____12538 with
                             | (t21,ty2,g2) ->
                                 let uu____12551 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12551
                                   (fun uu____12558  ->
                                      let uu____12559 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12559
                                        (fun uu____12567  ->
                                           let uu____12568 =
                                             do_unify e ty1 ty2  in
                                           let uu____12572 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12568 uu____12572)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12475
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12620  ->
             let uu____12621 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12621
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
        (fun uu____12655  ->
           let uu____12656 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12656)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12667 =
      mlog
        (fun uu____12672  ->
           let uu____12673 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12673)
        (fun uu____12678  ->
           let uu____12679 = cur_goal ()  in
           bind uu____12679
             (fun g  ->
                let uu____12685 =
                  let uu____12694 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12694 ty  in
                bind uu____12685
                  (fun uu____12706  ->
                     match uu____12706 with
                     | (ty1,uu____12716,guard) ->
                         let uu____12718 =
                           let uu____12721 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12721 guard  in
                         bind uu____12718
                           (fun uu____12725  ->
                              let uu____12726 =
                                let uu____12730 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12731 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12730 uu____12731 ty1  in
                              bind uu____12726
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12740 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12740
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12747 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12748 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12747
                                          uu____12748
                                         in
                                      let nty =
                                        let uu____12750 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12750 ty1  in
                                      let uu____12751 =
                                        let uu____12755 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12755 ng nty  in
                                      bind uu____12751
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12764 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12764
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12667
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12838 =
      let uu____12847 = cur_goal ()  in
      bind uu____12847
        (fun g  ->
           let uu____12859 =
             let uu____12868 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12868 s_tm  in
           bind uu____12859
             (fun uu____12886  ->
                match uu____12886 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12904 =
                      let uu____12907 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12907 guard  in
                    bind uu____12904
                      (fun uu____12920  ->
                         let uu____12921 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12921 with
                         | (h,args) ->
                             let uu____12966 =
                               let uu____12973 =
                                 let uu____12974 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12974.FStar_Syntax_Syntax.n  in
                               match uu____12973 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12989;
                                      FStar_Syntax_Syntax.vars = uu____12990;_},us)
                                   -> ret (fv, us)
                               | uu____13000 -> fail "type is not an fv"  in
                             bind uu____12966
                               (fun uu____13021  ->
                                  match uu____13021 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____13037 =
                                        let uu____13040 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____13040 t_lid
                                         in
                                      (match uu____13037 with
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
                                                  (fun uu____13091  ->
                                                     let uu____13092 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____13092 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____13107 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____13135
                                                                  =
                                                                  let uu____13138
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13138
                                                                    c_lid
                                                                   in
                                                                match uu____13135
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
                                                                    uu____13212
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
                                                                    let uu____13217
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13217
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13240
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13240
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13283
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____13283
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____13356
                                                                    =
                                                                    let uu____13358
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____13358
                                                                     in
                                                                    failwhen
                                                                    uu____13356
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13377
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
                                                                    uu___5_13394
                                                                    =
                                                                    match uu___5_13394
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13398)
                                                                    -> true
                                                                    | 
                                                                    uu____13401
                                                                    -> false
                                                                     in
                                                                    let uu____13405
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13405
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
                                                                    uu____13539
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
                                                                    uu____13601
                                                                     ->
                                                                    match uu____13601
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13621),
                                                                    (t,uu____13623))
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
                                                                    uu____13693
                                                                     ->
                                                                    match uu____13693
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13720),
                                                                    (t,uu____13722))
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
                                                                    uu____13781
                                                                     ->
                                                                    match uu____13781
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
                                                                    let uu____13836
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1899_13853
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1899_13853.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13836
                                                                    with
                                                                    | 
                                                                    (uu____13867,uu____13868,uu____13869,pat_t,uu____13871,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13878
                                                                    =
                                                                    let uu____13879
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13879
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13878
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13884
                                                                    =
                                                                    let uu____13893
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13893]
                                                                     in
                                                                    let uu____13912
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13884
                                                                    uu____13912
                                                                     in
                                                                    let nty =
                                                                    let uu____13918
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13918
                                                                     in
                                                                    let uu____13921
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13921
                                                                    (fun
                                                                    uu____13951
                                                                     ->
                                                                    match uu____13951
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
                                                                    let uu____13978
                                                                    =
                                                                    let uu____13989
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13989]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13978
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____14025
                                                                    =
                                                                    let uu____14036
                                                                    =
                                                                    let uu____14041
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____14041)
                                                                     in
                                                                    (g', br,
                                                                    uu____14036)
                                                                     in
                                                                    ret
                                                                    uu____14025))))))
                                                                    | 
                                                                    uu____14062
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____13107
                                                           (fun goal_brs  ->
                                                              let uu____14112
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____14112
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
                                                                  let uu____14185
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____14185
                                                                    (
                                                                    fun
                                                                    uu____14196
                                                                     ->
                                                                    let uu____14197
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14197
                                                                    (fun
                                                                    uu____14207
                                                                     ->
                                                                    ret infos))))
                                            | uu____14214 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12838
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14263::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14293 = init xs  in x :: uu____14293
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14306 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14315) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14381 = last args  in
          (match uu____14381 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14411 =
                 let uu____14412 =
                   let uu____14417 =
                     let uu____14418 =
                       let uu____14423 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14423  in
                     uu____14418 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14417, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14412  in
               FStar_All.pipe_left ret uu____14411)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14434,uu____14435) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14488 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14488 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14530 =
                      let uu____14531 =
                        let uu____14536 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14536)  in
                      FStar_Reflection_Data.Tv_Abs uu____14531  in
                    FStar_All.pipe_left ret uu____14530))
      | FStar_Syntax_Syntax.Tm_type uu____14539 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14564 ->
          let uu____14579 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14579 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14610 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14610 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14663 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14676 =
            let uu____14677 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14677  in
          FStar_All.pipe_left ret uu____14676
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14698 =
            let uu____14699 =
              let uu____14704 =
                let uu____14705 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14705  in
              (uu____14704, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14699  in
          FStar_All.pipe_left ret uu____14698
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14745 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14750 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14750 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14803 ->
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
             | FStar_Util.Inr uu____14845 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14849 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14849 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14869 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14875 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14930 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14930
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14951 =
                  let uu____14958 =
                    FStar_List.map
                      (fun uu____14971  ->
                         match uu____14971 with
                         | (p1,uu____14980) -> inspect_pat p1) ps
                     in
                  (fv, uu____14958)  in
                FStar_Reflection_Data.Pat_Cons uu____14951
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
              (fun uu___6_15076  ->
                 match uu___6_15076 with
                 | (pat,uu____15098,t5) ->
                     let uu____15116 = inspect_pat pat  in (uu____15116, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____15125 ->
          ((let uu____15127 =
              let uu____15133 =
                let uu____15135 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15137 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15135 uu____15137
                 in
              (FStar_Errors.Warning_CantInspect, uu____15133)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15127);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14306
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15155 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15155
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15159 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15159
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15163 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15163
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15170 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15170
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15195 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15195
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15212 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15212
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15231 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15231
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15235 =
          let uu____15236 =
            let uu____15243 =
              let uu____15244 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15244  in
            FStar_Syntax_Syntax.mk uu____15243  in
          uu____15236 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15235
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15249 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15249
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15260 =
          let uu____15261 =
            let uu____15268 =
              let uu____15269 =
                let uu____15283 =
                  let uu____15286 =
                    let uu____15287 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15287]  in
                  FStar_Syntax_Subst.close uu____15286 t2  in
                ((false, [lb]), uu____15283)  in
              FStar_Syntax_Syntax.Tm_let uu____15269  in
            FStar_Syntax_Syntax.mk uu____15268  in
          uu____15261 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15260
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15329 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15329 with
         | (lbs,body) ->
             let uu____15344 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15344)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15381 =
                let uu____15382 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15382  in
              FStar_All.pipe_left wrap uu____15381
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15389 =
                let uu____15390 =
                  let uu____15404 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15422 = pack_pat p1  in
                         (uu____15422, false)) ps
                     in
                  (fv, uu____15404)  in
                FStar_Syntax_Syntax.Pat_cons uu____15390  in
              FStar_All.pipe_left wrap uu____15389
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
            (fun uu___7_15471  ->
               match uu___7_15471 with
               | (pat,t1) ->
                   let uu____15488 = pack_pat pat  in
                   (uu____15488, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15536 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15536
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15564 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15564
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15610 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15610
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15649 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15649
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15669 =
        bind get
          (fun ps  ->
             let uu____15675 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15675 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15669
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15709 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2197_15716 = ps  in
                 let uu____15717 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2197_15716.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2197_15716.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2197_15716.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2197_15716.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2197_15716.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2197_15716.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2197_15716.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2197_15716.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2197_15716.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2197_15716.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2197_15716.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2197_15716.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15717
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15709
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15744 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15744 with
      | (u,ctx_uvars,g_u) ->
          let uu____15777 = FStar_List.hd ctx_uvars  in
          (match uu____15777 with
           | (ctx_uvar,uu____15791) ->
               let g =
                 let uu____15793 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15793 false
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
        let uu____15816 = goal_of_goal_ty env typ  in
        match uu____15816 with
        | (g,g_u) ->
            let ps =
              let uu____15828 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15831 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15828;
                FStar_Tactics_Types.local_state = uu____15831
              }  in
            let uu____15841 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15841)
  