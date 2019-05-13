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
            ((let uu____559 =
                FStar_Common.string_of_list (fun s1  -> s1) seen  in
              FStar_Util.print1 "GG seen = %s\n" uu____559);
             (let uu____566 = FStar_Syntax_Subst.subst_binders subst1 [b]  in
              match uu____566 with
              | b1::[] ->
                  let uu____610 = b1  in
                  (match uu____610 with
                   | (bv0,q) ->
                       let nbs =
                         fresh_until (s bv0)
                           (fun s1  ->
                              Prims.op_Negation (FStar_List.mem s1 seen))
                          in
                       let bv = sset bv0 nbs  in
                       let b2 = (bv, q)  in
                       let uu____651 =
                         let uu____654 =
                           let uu____657 =
                             let uu____658 =
                               let uu____665 =
                                 FStar_Syntax_Syntax.bv_to_name bv  in
                               (bv0, uu____665)  in
                             FStar_Syntax_Syntax.NT uu____658  in
                           [uu____657]  in
                         FStar_List.append subst1 uu____654  in
                       go (nbs :: seen) uu____651 bs2 (b2 :: bs') t1)))
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
            let uu____727 = FStar_Options.print_implicits ()  in
            if uu____727
            then
              let uu____731 = FStar_Tactics_Types.goal_env g  in
              let uu____732 = FStar_Tactics_Types.goal_witness g  in
              tts uu____731 uu____732
            else
              (let uu____735 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____735 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____741 = FStar_Tactics_Types.goal_env g  in
                   let uu____742 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____741 uu____742)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____765 = FStar_Util.string_of_int i  in
                let uu____767 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____765 uu____767
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
          let uu____791 = unshadow goal_binders goal_ty  in
          match uu____791 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____805 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____808 =
                     let uu____810 = FStar_Tactics_Types.goal_env g  in
                     tts uu____810 goal_ty1  in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____805 w uu____808)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____837 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____837
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____862 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____862
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____894 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____894
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____907 =
      let uu____908 = FStar_Tactics_Types.goal_env g  in
      let uu____909 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____908 uu____909  in
    FStar_Syntax_Util.un_squash uu____907
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____918 = get_phi g  in FStar_Option.isSome uu____918 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____942  ->
    bind get
      (fun ps  ->
         let uu____950 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____950)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____965  ->
    match uu____965 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____987 =
          let uu____991 =
            let uu____995 =
              let uu____997 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____997
                msg
               in
            let uu____1000 =
              let uu____1004 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____1008 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____1008
                else ""  in
              let uu____1014 =
                let uu____1018 =
                  let uu____1020 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____1020
                  then
                    let uu____1025 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____1025
                  else ""  in
                [uu____1018]  in
              uu____1004 :: uu____1014  in
            uu____995 :: uu____1000  in
          let uu____1035 =
            let uu____1039 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____1059 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____1039 uu____1059  in
          FStar_List.append uu____991 uu____1035  in
        FStar_String.concat "" uu____987
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____1098 = unshadow g_binders g_type  in
    match uu____1098 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____1106 =
            let uu____1107 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____1107  in
          FStar_Syntax_Print.binders_to_json uu____1106 g_binders1  in
        let uu____1108 =
          let uu____1116 =
            let uu____1124 =
              let uu____1130 =
                let uu____1131 =
                  let uu____1139 =
                    let uu____1145 =
                      let uu____1146 =
                        let uu____1148 = FStar_Tactics_Types.goal_env g  in
                        let uu____1149 = FStar_Tactics_Types.goal_witness g
                           in
                        tts uu____1148 uu____1149  in
                      FStar_Util.JsonStr uu____1146  in
                    ("witness", uu____1145)  in
                  let uu____1152 =
                    let uu____1160 =
                      let uu____1166 =
                        let uu____1167 =
                          let uu____1169 = FStar_Tactics_Types.goal_env g  in
                          tts uu____1169 g_type1  in
                        FStar_Util.JsonStr uu____1167  in
                      ("type", uu____1166)  in
                    [uu____1160;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____1139 :: uu____1152  in
                FStar_Util.JsonAssoc uu____1131  in
              ("goal", uu____1130)  in
            [uu____1124]  in
          ("hyps", j_binders) :: uu____1116  in
        FStar_Util.JsonAssoc uu____1108
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____1223  ->
    match uu____1223 with
    | (msg,ps) ->
        let uu____1233 =
          let uu____1241 =
            let uu____1249 =
              let uu____1257 =
                let uu____1265 =
                  let uu____1271 =
                    let uu____1272 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____1272  in
                  ("goals", uu____1271)  in
                let uu____1277 =
                  let uu____1285 =
                    let uu____1291 =
                      let uu____1292 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____1292  in
                    ("smt-goals", uu____1291)  in
                  [uu____1285]  in
                uu____1265 :: uu____1277  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____1257
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____1249  in
          let uu____1326 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____1342 =
                let uu____1348 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____1348)  in
              [uu____1342]
            else []  in
          FStar_List.append uu____1241 uu____1326  in
        FStar_Util.JsonAssoc uu____1233
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1388  ->
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
         (let uu____1419 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____1419 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1492 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1492
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1506 . Prims.string -> Prims.string -> 'Auu____1506 tac =
  fun msg  ->
    fun x  -> let uu____1523 = FStar_Util.format1 msg x  in fail uu____1523
  
let fail2 :
  'Auu____1534 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1534 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1558 = FStar_Util.format2 msg x y  in fail uu____1558
  
let fail3 :
  'Auu____1571 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1571 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1602 = FStar_Util.format3 msg x y z  in fail uu____1602
  
let fail4 :
  'Auu____1617 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1617 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1655 = FStar_Util.format4 msg x y z w  in
            fail uu____1655
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1690 = run t ps  in
         match uu____1690 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___229_1714 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___229_1714.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___229_1714.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___229_1714.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___229_1714.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___229_1714.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___229_1714.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___229_1714.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___229_1714.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___229_1714.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___229_1714.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___229_1714.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___229_1714.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1753 = run t ps  in
         match uu____1753 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1801 = catch t  in
    bind uu____1801
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1828 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___255_1860  ->
              match () with
              | () -> let uu____1865 = trytac t  in run uu____1865 ps) ()
         with
         | FStar_Errors.Err (uu____1881,msg) ->
             (log ps
                (fun uu____1887  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1893,msg,uu____1895) ->
             (log ps
                (fun uu____1900  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1937 = run t ps  in
           match uu____1937 with
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
  fun p  -> mk_tac (fun uu____1961  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___290_1976 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___290_1976.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___290_1976.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___290_1976.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___290_1976.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___290_1976.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___290_1976.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___290_1976.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___290_1976.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___290_1976.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___290_1976.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___290_1976.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___290_1976.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____2000 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____2000
         then
           let uu____2004 = FStar_Syntax_Print.term_to_string t1  in
           let uu____2006 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____2004
             uu____2006
         else ());
        (try
           (fun uu___298_2017  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____2025 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2025
                    then
                      let uu____2029 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____2031 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____2033 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____2029
                        uu____2031 uu____2033
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____2044 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____2044 (fun uu____2049  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____2059,msg) ->
             mlog
               (fun uu____2065  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____2068  -> ret false)
         | FStar_Errors.Error (uu____2071,msg,r) ->
             mlog
               (fun uu____2079  ->
                  let uu____2080 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____2080) (fun uu____2084  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___324_2098 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___324_2098.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___324_2098.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___324_2098.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___328_2101 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___328_2101.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___328_2101.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___328_2101.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___328_2101.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___328_2101.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___328_2101.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___328_2101.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___328_2101.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___328_2101.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___328_2101.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___328_2101.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___328_2101.FStar_Tactics_Types.local_state)
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
          (fun uu____2128  ->
             (let uu____2130 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____2130
              then
                (FStar_Options.push ();
                 (let uu____2135 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____2139 = __do_unify env t1 t2  in
              bind uu____2139
                (fun r  ->
                   (let uu____2150 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2150 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___343_2164 = ps  in
         let uu____2165 =
           FStar_List.filter
             (fun g  ->
                let uu____2171 = check_goal_solved g  in
                FStar_Option.isNone uu____2171) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___343_2164.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___343_2164.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___343_2164.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2165;
           FStar_Tactics_Types.smt_goals =
             (uu___343_2164.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___343_2164.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___343_2164.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___343_2164.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___343_2164.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___343_2164.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___343_2164.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___343_2164.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___343_2164.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2189 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____2189 with
      | FStar_Pervasives_Native.Some uu____2194 ->
          let uu____2195 =
            let uu____2197 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____2197  in
          fail uu____2195
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____2218 = FStar_Tactics_Types.goal_env goal  in
      let uu____2219 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____2218 solution uu____2219
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____2226 =
         let uu___356_2227 = p  in
         let uu____2228 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___356_2227.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___356_2227.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___356_2227.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2228;
           FStar_Tactics_Types.smt_goals =
             (uu___356_2227.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___356_2227.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___356_2227.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___356_2227.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___356_2227.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___356_2227.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___356_2227.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___356_2227.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___356_2227.FStar_Tactics_Types.local_state)
         }  in
       set uu____2226)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____2250  ->
           let uu____2251 =
             let uu____2253 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____2253  in
           let uu____2254 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____2251 uu____2254)
        (fun uu____2259  ->
           let uu____2260 = trysolve goal solution  in
           bind uu____2260
             (fun b  ->
                if b
                then bind __dismiss (fun uu____2272  -> remove_solved_goals)
                else
                  (let uu____2275 =
                     let uu____2277 =
                       let uu____2279 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____2279 solution  in
                     let uu____2280 =
                       let uu____2282 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2283 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____2282 uu____2283  in
                     let uu____2284 =
                       let uu____2286 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2287 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____2286 uu____2287  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____2277 uu____2280 uu____2284
                      in
                   fail uu____2275)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2304 = set_solution goal solution  in
      bind uu____2304
        (fun uu____2308  ->
           bind __dismiss (fun uu____2310  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___372_2329 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_2329.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_2329.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_2329.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___372_2329.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_2329.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_2329.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_2329.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_2329.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_2329.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_2329.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_2329.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_2329.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___376_2348 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___376_2348.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___376_2348.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___376_2348.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___376_2348.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___376_2348.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___376_2348.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___376_2348.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___376_2348.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___376_2348.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___376_2348.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___376_2348.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___376_2348.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2364 = FStar_Options.defensive ()  in
    if uu____2364
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2374 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2374)
         in
      let b2 =
        b1 &&
          (let uu____2378 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2378)
         in
      let rec aux b3 e =
        let uu____2393 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2393 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2413 =
        (let uu____2417 = aux b2 env  in Prims.op_Negation uu____2417) &&
          (let uu____2420 = FStar_ST.op_Bang nwarn  in
           uu____2420 < (Prims.parse_int "5"))
         in
      (if uu____2413
       then
         ((let uu____2446 =
             let uu____2447 = FStar_Tactics_Types.goal_type g  in
             uu____2447.FStar_Syntax_Syntax.pos  in
           let uu____2450 =
             let uu____2456 =
               let uu____2458 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2458
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2456)  in
           FStar_Errors.log_issue uu____2446 uu____2450);
          (let uu____2462 =
             let uu____2464 = FStar_ST.op_Bang nwarn  in
             uu____2464 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____2462))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___398_2533 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___398_2533.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___398_2533.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___398_2533.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___398_2533.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___398_2533.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___398_2533.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___398_2533.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___398_2533.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___398_2533.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___398_2533.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___398_2533.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___398_2533.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___403_2554 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___403_2554.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___403_2554.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___403_2554.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___403_2554.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___403_2554.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___403_2554.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___403_2554.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___403_2554.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___403_2554.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___403_2554.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___403_2554.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___403_2554.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___408_2575 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___408_2575.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___408_2575.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___408_2575.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___408_2575.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___408_2575.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___408_2575.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___408_2575.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___408_2575.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___408_2575.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___408_2575.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___408_2575.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___408_2575.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___413_2596 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___413_2596.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___413_2596.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___413_2596.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___413_2596.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___413_2596.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___413_2596.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___413_2596.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___413_2596.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___413_2596.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___413_2596.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___413_2596.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___413_2596.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2608  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2639 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2639 with
        | (u,ctx_uvar,g_u) ->
            let uu____2677 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2677
              (fun uu____2686  ->
                 let uu____2687 =
                   let uu____2692 =
                     let uu____2693 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2693  in
                   (u, uu____2692)  in
                 ret uu____2687)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2714 = FStar_Syntax_Util.un_squash t1  in
    match uu____2714 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2726 =
          let uu____2727 = FStar_Syntax_Subst.compress t'1  in
          uu____2727.FStar_Syntax_Syntax.n  in
        (match uu____2726 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2732 -> false)
    | uu____2734 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2747 = FStar_Syntax_Util.un_squash t  in
    match uu____2747 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2758 =
          let uu____2759 = FStar_Syntax_Subst.compress t'  in
          uu____2759.FStar_Syntax_Syntax.n  in
        (match uu____2758 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2764 -> false)
    | uu____2766 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2779  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2791 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2791 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2798 = goal_to_string_verbose hd1  in
                    let uu____2800 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2798 uu____2800);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2813 =
      bind get
        (fun ps  ->
           let uu____2819 = cur_goal ()  in
           bind uu____2819
             (fun g  ->
                (let uu____2826 =
                   let uu____2827 = FStar_Tactics_Types.goal_type g  in
                   uu____2827.FStar_Syntax_Syntax.pos  in
                 let uu____2830 =
                   let uu____2836 =
                     let uu____2838 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2838
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2836)  in
                 FStar_Errors.log_issue uu____2826 uu____2830);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2813
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2861  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___458_2872 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___458_2872.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___458_2872.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___458_2872.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___458_2872.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___458_2872.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___458_2872.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___458_2872.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___458_2872.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___458_2872.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___458_2872.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___458_2872.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___458_2872.FStar_Tactics_Types.local_state)
           }  in
         let uu____2874 = set ps1  in
         bind uu____2874
           (fun uu____2879  ->
              let uu____2880 = FStar_BigInt.of_int_fs n1  in ret uu____2880))
  
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
              let uu____2918 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2918 phi  in
            let uu____2919 = new_uvar reason env typ  in
            bind uu____2919
              (fun uu____2934  ->
                 match uu____2934 with
                 | (uu____2941,ctx_uvar) ->
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
             (fun uu____2988  ->
                let uu____2989 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2989)
             (fun uu____2994  ->
                let e1 =
                  let uu___476_2996 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___476_2996.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___476_2996.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___476_2996.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___476_2996.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___476_2996.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___476_2996.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___476_2996.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___476_2996.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___476_2996.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___476_2996.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___476_2996.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___476_2996.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___476_2996.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___476_2996.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___476_2996.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___476_2996.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___476_2996.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___476_2996.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___476_2996.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___476_2996.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___476_2996.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___476_2996.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___476_2996.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___476_2996.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___476_2996.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___476_2996.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___476_2996.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___476_2996.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___476_2996.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___476_2996.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___476_2996.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___476_2996.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___476_2996.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___476_2996.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___476_2996.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___476_2996.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___476_2996.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___476_2996.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___476_2996.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___476_2996.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___476_2996.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___476_2996.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___480_3008  ->
                     match () with
                     | () ->
                         let uu____3017 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3017) ()
                with
                | FStar_Errors.Err (uu____3044,msg) ->
                    let uu____3048 = tts e1 t  in
                    let uu____3050 =
                      let uu____3052 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3052
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3048 uu____3050 msg
                | FStar_Errors.Error (uu____3062,msg,uu____3064) ->
                    let uu____3067 = tts e1 t  in
                    let uu____3069 =
                      let uu____3071 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3071
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3067 uu____3069 msg))
  
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
             (fun uu____3124  ->
                let uu____3125 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3125)
             (fun uu____3130  ->
                let e1 =
                  let uu___497_3132 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___497_3132.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___497_3132.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___497_3132.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___497_3132.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___497_3132.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___497_3132.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___497_3132.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___497_3132.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___497_3132.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___497_3132.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___497_3132.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___497_3132.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___497_3132.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___497_3132.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___497_3132.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___497_3132.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___497_3132.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___497_3132.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___497_3132.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___497_3132.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___497_3132.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___497_3132.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___497_3132.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___497_3132.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___497_3132.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___497_3132.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___497_3132.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___497_3132.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___497_3132.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___497_3132.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___497_3132.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___497_3132.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___497_3132.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___497_3132.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___497_3132.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___497_3132.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___497_3132.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___497_3132.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___497_3132.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___497_3132.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___497_3132.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___497_3132.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___501_3147  ->
                     match () with
                     | () ->
                         let uu____3156 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3156 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3194,msg) ->
                    let uu____3198 = tts e1 t  in
                    let uu____3200 =
                      let uu____3202 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3202
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3198 uu____3200 msg
                | FStar_Errors.Error (uu____3212,msg,uu____3214) ->
                    let uu____3217 = tts e1 t  in
                    let uu____3219 =
                      let uu____3221 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3221
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3217 uu____3219 msg))
  
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
             (fun uu____3274  ->
                let uu____3275 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3275)
             (fun uu____3281  ->
                let e1 =
                  let uu___522_3283 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___522_3283.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___522_3283.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___522_3283.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___522_3283.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___522_3283.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___522_3283.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___522_3283.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___522_3283.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___522_3283.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___522_3283.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___522_3283.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___522_3283.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___522_3283.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___522_3283.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___522_3283.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___522_3283.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___522_3283.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___522_3283.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___522_3283.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___522_3283.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___522_3283.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___522_3283.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___522_3283.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___522_3283.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___522_3283.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___522_3283.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___522_3283.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___522_3283.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___522_3283.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___522_3283.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___522_3283.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___522_3283.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___522_3283.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___522_3283.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___522_3283.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___522_3283.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___522_3283.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___522_3283.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___522_3283.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___522_3283.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___522_3283.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___522_3283.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___525_3286 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___525_3286.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___525_3286.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___525_3286.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___525_3286.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___525_3286.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___525_3286.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___525_3286.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___525_3286.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___525_3286.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___525_3286.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___525_3286.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___525_3286.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___525_3286.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___525_3286.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___525_3286.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___525_3286.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___525_3286.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___525_3286.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___525_3286.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___525_3286.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___525_3286.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___525_3286.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___525_3286.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___525_3286.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___525_3286.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___525_3286.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___525_3286.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___525_3286.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___525_3286.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___525_3286.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___525_3286.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___525_3286.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___525_3286.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___525_3286.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___525_3286.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___525_3286.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___525_3286.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___525_3286.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___525_3286.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___525_3286.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___525_3286.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___525_3286.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___529_3298  ->
                     match () with
                     | () ->
                         let uu____3307 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3307) ()
                with
                | FStar_Errors.Err (uu____3334,msg) ->
                    let uu____3338 = tts e2 t  in
                    let uu____3340 =
                      let uu____3342 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3342
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3338 uu____3340 msg
                | FStar_Errors.Error (uu____3352,msg,uu____3354) ->
                    let uu____3357 = tts e2 t  in
                    let uu____3359 =
                      let uu____3361 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3361
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3357 uu____3359 msg))
  
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
  fun uu____3395  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___550_3414 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___550_3414.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___550_3414.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___550_3414.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___550_3414.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___550_3414.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___550_3414.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___550_3414.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___550_3414.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___550_3414.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___550_3414.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___550_3414.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___550_3414.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3439 = get_guard_policy ()  in
      bind uu____3439
        (fun old_pol  ->
           let uu____3445 = set_guard_policy pol  in
           bind uu____3445
             (fun uu____3449  ->
                bind t
                  (fun r  ->
                     let uu____3453 = set_guard_policy old_pol  in
                     bind uu____3453 (fun uu____3457  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3461 = let uu____3466 = cur_goal ()  in trytac uu____3466  in
  bind uu____3461
    (fun uu___0_3473  ->
       match uu___0_3473 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3479 = FStar_Options.peek ()  in ret uu____3479)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3504  ->
             let uu____3505 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3505)
          (fun uu____3510  ->
             let uu____3511 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3511
               (fun uu____3515  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3519 =
                         let uu____3520 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3520.FStar_TypeChecker_Env.guard_f  in
                       match uu____3519 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3524 = istrivial e f  in
                           if uu____3524
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3537 =
                                          let uu____3543 =
                                            let uu____3545 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3545
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3543)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3537);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3551  ->
                                           let uu____3552 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3552)
                                        (fun uu____3557  ->
                                           let uu____3558 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3558
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___579_3566 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___579_3566.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___579_3566.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___579_3566.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___579_3566.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3570  ->
                                           let uu____3571 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3571)
                                        (fun uu____3576  ->
                                           let uu____3577 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3577
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___586_3585 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___586_3585.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___586_3585.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___586_3585.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___586_3585.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3589  ->
                                           let uu____3590 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3590)
                                        (fun uu____3594  ->
                                           try
                                             (fun uu___593_3599  ->
                                                match () with
                                                | () ->
                                                    let uu____3602 =
                                                      let uu____3604 =
                                                        let uu____3606 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3606
                                                         in
                                                      Prims.op_Negation
                                                        uu____3604
                                                       in
                                                    if uu____3602
                                                    then
                                                      mlog
                                                        (fun uu____3613  ->
                                                           let uu____3614 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3614)
                                                        (fun uu____3618  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___592_3623 ->
                                               mlog
                                                 (fun uu____3628  ->
                                                    let uu____3629 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3629)
                                                 (fun uu____3633  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____3645 =
      let uu____3648 = cur_goal ()  in
      bind uu____3648
        (fun goal  ->
           let uu____3654 =
             let uu____3663 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3663 t  in
           bind uu____3654
             (fun uu____3675  ->
                match uu____3675 with
                | (uu____3684,lc,uu____3686) ->
                    let uu____3687 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____3687))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____3645
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3703 =
      let uu____3708 = tcc t  in
      bind uu____3708 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3703
  
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
            let uu____3760 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3760 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3772  ->
    let uu____3775 = cur_goal ()  in
    bind uu____3775
      (fun goal  ->
         let uu____3781 =
           let uu____3783 = FStar_Tactics_Types.goal_env goal  in
           let uu____3784 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3783 uu____3784  in
         if uu____3781
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3790 =
              let uu____3792 = FStar_Tactics_Types.goal_env goal  in
              let uu____3793 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3792 uu____3793  in
            fail1 "Not a trivial goal: %s" uu____3790))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3844 =
               try
                 (fun uu___651_3867  ->
                    match () with
                    | () ->
                        let uu____3878 =
                          let uu____3887 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3887
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3878) ()
               with | uu___650_3898 -> fail "divide: not enough goals"  in
             bind uu____3844
               (fun uu____3935  ->
                  match uu____3935 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___633_3961 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___633_3961.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___633_3961.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___633_3961.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___633_3961.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___633_3961.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___633_3961.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___633_3961.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___633_3961.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___633_3961.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___633_3961.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___633_3961.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3962 = set lp  in
                      bind uu____3962
                        (fun uu____3970  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___639_3986 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___639_3986.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___639_3986.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___639_3986.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___639_3986.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___639_3986.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___639_3986.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___639_3986.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___639_3986.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___639_3986.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___639_3986.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___639_3986.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3987 = set rp  in
                                     bind uu____3987
                                       (fun uu____3995  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___645_4011 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___645_4011.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___645_4011.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4012 = set p'
                                                       in
                                                    bind uu____4012
                                                      (fun uu____4020  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4026 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4048 = divide FStar_BigInt.one f idtac  in
    bind uu____4048
      (fun uu____4061  -> match uu____4061 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4099::uu____4100 ->
             let uu____4103 =
               let uu____4112 = map tau  in
               divide FStar_BigInt.one tau uu____4112  in
             bind uu____4103
               (fun uu____4130  ->
                  match uu____4130 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4172 =
        bind t1
          (fun uu____4177  ->
             let uu____4178 = map t2  in
             bind uu____4178 (fun uu____4186  -> ret ()))
         in
      focus uu____4172
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4196  ->
    let uu____4199 =
      let uu____4202 = cur_goal ()  in
      bind uu____4202
        (fun goal  ->
           let uu____4211 =
             let uu____4218 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4218  in
           match uu____4211 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4227 =
                 let uu____4229 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4229  in
               if uu____4227
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4238 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4238 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4254 = new_uvar "intro" env' typ'  in
                  bind uu____4254
                    (fun uu____4271  ->
                       match uu____4271 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4295 = set_solution goal sol  in
                           bind uu____4295
                             (fun uu____4301  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4303 =
                                  let uu____4306 = bnorm_goal g  in
                                  replace_cur uu____4306  in
                                bind uu____4303 (fun uu____4308  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4313 =
                 let uu____4315 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4316 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4315 uu____4316  in
               fail1 "goal is not an arrow (%s)" uu____4313)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4199
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4334  ->
    let uu____4341 = cur_goal ()  in
    bind uu____4341
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4360 =
            let uu____4367 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4367  in
          match uu____4360 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4380 =
                let uu____4382 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4382  in
              if uu____4380
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4399 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4399
                    in
                 let bs =
                   let uu____4410 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4410; b]  in
                 let env' =
                   let uu____4436 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4436 bs  in
                 let uu____4437 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4437
                   (fun uu____4463  ->
                      match uu____4463 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4477 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4480 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4477
                              FStar_Parser_Const.effect_Tot_lid uu____4480 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4498 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4498 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4520 =
                                   let uu____4521 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4521.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4520
                                  in
                               let uu____4537 = set_solution goal tm  in
                               bind uu____4537
                                 (fun uu____4546  ->
                                    let uu____4547 =
                                      let uu____4550 =
                                        bnorm_goal
                                          (let uu___716_4553 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___716_4553.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___716_4553.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___716_4553.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___716_4553.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4550  in
                                    bind uu____4547
                                      (fun uu____4560  ->
                                         let uu____4561 =
                                           let uu____4566 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4566, b)  in
                                         ret uu____4561)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4575 =
                let uu____4577 = FStar_Tactics_Types.goal_env goal  in
                let uu____4578 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4577 uu____4578  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4575))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4598 = cur_goal ()  in
    bind uu____4598
      (fun goal  ->
         mlog
           (fun uu____4605  ->
              let uu____4606 =
                let uu____4608 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4608  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4606)
           (fun uu____4614  ->
              let steps =
                let uu____4618 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4618
                 in
              let t =
                let uu____4622 = FStar_Tactics_Types.goal_env goal  in
                let uu____4623 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4622 uu____4623  in
              let uu____4624 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4624))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4649 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4657 -> g.FStar_Tactics_Types.opts
                 | uu____4660 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4665  ->
                    let uu____4666 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4666)
                 (fun uu____4671  ->
                    let uu____4672 = __tc_lax e t  in
                    bind uu____4672
                      (fun uu____4693  ->
                         match uu____4693 with
                         | (t1,uu____4703,uu____4704) ->
                             let steps =
                               let uu____4708 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4708
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4714  ->
                                  let uu____4715 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4715)
                               (fun uu____4719  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4649
  
let (refine_intro : unit -> unit tac) =
  fun uu____4732  ->
    let uu____4735 =
      let uu____4738 = cur_goal ()  in
      bind uu____4738
        (fun g  ->
           let uu____4745 =
             let uu____4756 = FStar_Tactics_Types.goal_env g  in
             let uu____4757 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4756 uu____4757
              in
           match uu____4745 with
           | (uu____4760,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4786 =
                 let uu____4791 =
                   let uu____4796 =
                     let uu____4797 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4797]  in
                   FStar_Syntax_Subst.open_term uu____4796 phi  in
                 match uu____4791 with
                 | (bvs,phi1) ->
                     let uu____4822 =
                       let uu____4823 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4823  in
                     (uu____4822, phi1)
                  in
               (match uu____4786 with
                | (bv1,phi1) ->
                    let uu____4842 =
                      let uu____4845 = FStar_Tactics_Types.goal_env g  in
                      let uu____4846 =
                        let uu____4847 =
                          let uu____4850 =
                            let uu____4851 =
                              let uu____4858 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4858)  in
                            FStar_Syntax_Syntax.NT uu____4851  in
                          [uu____4850]  in
                        FStar_Syntax_Subst.subst uu____4847 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4845
                        uu____4846 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4842
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4867  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4735
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4890 = cur_goal ()  in
      bind uu____4890
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4899 = FStar_Tactics_Types.goal_env goal  in
               let uu____4900 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4899 uu____4900
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4903 = __tc env t  in
           bind uu____4903
             (fun uu____4922  ->
                match uu____4922 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4937  ->
                         let uu____4938 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4940 =
                           let uu____4942 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4942
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4938 uu____4940)
                      (fun uu____4946  ->
                         let uu____4947 =
                           let uu____4950 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4950 guard  in
                         bind uu____4947
                           (fun uu____4953  ->
                              mlog
                                (fun uu____4957  ->
                                   let uu____4958 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4960 =
                                     let uu____4962 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4962
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4958 uu____4960)
                                (fun uu____4966  ->
                                   let uu____4967 =
                                     let uu____4971 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4972 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4971 typ uu____4972  in
                                   bind uu____4967
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4982 =
                                             let uu____4984 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4984 t1  in
                                           let uu____4985 =
                                             let uu____4987 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4987 typ  in
                                           let uu____4988 =
                                             let uu____4990 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4991 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4990 uu____4991  in
                                           let uu____4992 =
                                             let uu____4994 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4995 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4994 uu____4995  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4982 uu____4985 uu____4988
                                             uu____4992)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5021 =
          mlog
            (fun uu____5026  ->
               let uu____5027 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5027)
            (fun uu____5032  ->
               let uu____5033 =
                 let uu____5040 = __exact_now set_expected_typ1 tm  in
                 catch uu____5040  in
               bind uu____5033
                 (fun uu___2_5049  ->
                    match uu___2_5049 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5060  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5064  ->
                             let uu____5065 =
                               let uu____5072 =
                                 let uu____5075 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5075
                                   (fun uu____5080  ->
                                      let uu____5081 = refine_intro ()  in
                                      bind uu____5081
                                        (fun uu____5085  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5072  in
                             bind uu____5065
                               (fun uu___1_5092  ->
                                  match uu___1_5092 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5101  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5104  -> ret ())
                                  | FStar_Util.Inl uu____5105 ->
                                      mlog
                                        (fun uu____5107  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5110  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5021
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5162 = f x  in
          bind uu____5162
            (fun y  ->
               let uu____5170 = mapM f xs  in
               bind uu____5170 (fun ys  -> ret (y :: ys)))
  
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
          let uu____5242 = do_unify e ty1 ty2  in
          bind uu____5242
            (fun uu___3_5256  ->
               if uu___3_5256
               then ret acc
               else
                 (let uu____5276 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____5276 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____5297 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____5299 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____5297
                        uu____5299
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____5316 =
                        let uu____5318 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____5318  in
                      if uu____5316
                      then fail "Codomain is effectful"
                      else
                        (let uu____5342 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____5342
                           (fun uu____5369  ->
                              match uu____5369 with
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
      let uu____5461 =
        mlog
          (fun uu____5466  ->
             let uu____5467 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5467)
          (fun uu____5472  ->
             let uu____5473 = cur_goal ()  in
             bind uu____5473
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5481 = __tc e tm  in
                  bind uu____5481
                    (fun uu____5502  ->
                       match uu____5502 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5515 =
                             let uu____5526 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5526  in
                           bind uu____5515
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____5564)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____5568 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5591  ->
                                       fun w  ->
                                         match uu____5591 with
                                         | (uvt,q,uu____5609) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5641 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5658  ->
                                       fun s  ->
                                         match uu____5658 with
                                         | (uu____5670,uu____5671,uv) ->
                                             let uu____5673 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5673) uvs uu____5641
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5683 = solve' goal w  in
                                bind uu____5683
                                  (fun uu____5688  ->
                                     let uu____5689 =
                                       mapM
                                         (fun uu____5706  ->
                                            match uu____5706 with
                                            | (uvt,q,uv) ->
                                                let uu____5718 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5718 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5723 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5724 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5724
                                                     then ret ()
                                                     else
                                                       (let uu____5731 =
                                                          let uu____5734 =
                                                            bnorm_goal
                                                              (let uu___877_5737
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___877_5737.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___877_5737.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___877_5737.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5734]  in
                                                        add_goals uu____5731)))
                                         uvs
                                        in
                                     bind uu____5689
                                       (fun uu____5742  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5461
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5770 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5770
    then
      let uu____5779 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5794 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5847 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5779 with
      | (pre,post) ->
          let post1 =
            let uu____5880 =
              let uu____5891 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5891]  in
            FStar_Syntax_Util.mk_app post uu____5880  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5922 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5922
       then
         let uu____5931 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5931
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
            let uu____6010 = f x e  in
            bind uu____6010 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6025 =
      let uu____6028 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6035  ->
                  let uu____6036 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6036)
               (fun uu____6042  ->
                  let is_unit_t t =
                    let uu____6050 =
                      let uu____6051 = FStar_Syntax_Subst.compress t  in
                      uu____6051.FStar_Syntax_Syntax.n  in
                    match uu____6050 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6057 -> false  in
                  let uu____6059 = cur_goal ()  in
                  bind uu____6059
                    (fun goal  ->
                       let uu____6065 =
                         let uu____6074 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6074 tm  in
                       bind uu____6065
                         (fun uu____6089  ->
                            match uu____6089 with
                            | (tm1,t,guard) ->
                                let uu____6101 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6101 with
                                 | (bs,comp) ->
                                     let uu____6134 = lemma_or_sq comp  in
                                     (match uu____6134 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6154 =
                                            fold_left
                                              (fun uu____6216  ->
                                                 fun uu____6217  ->
                                                   match (uu____6216,
                                                           uu____6217)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6368 =
                                                         is_unit_t b_t  in
                                                       if uu____6368
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
                                                         (let uu____6491 =
                                                            let uu____6498 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6498 b_t
                                                             in
                                                          bind uu____6491
                                                            (fun uu____6529 
                                                               ->
                                                               match uu____6529
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
                                          bind uu____6154
                                            (fun uu____6715  ->
                                               match uu____6715 with
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
                                                   let uu____6803 =
                                                     let uu____6807 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6808 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6809 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6807
                                                       uu____6808 uu____6809
                                                      in
                                                   bind uu____6803
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6820 =
                                                            let uu____6822 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6822
                                                              tm1
                                                             in
                                                          let uu____6823 =
                                                            let uu____6825 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6826 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____6825
                                                              uu____6826
                                                             in
                                                          let uu____6827 =
                                                            let uu____6829 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6830 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6829
                                                              uu____6830
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6820
                                                            uu____6823
                                                            uu____6827
                                                        else
                                                          (let uu____6834 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6834
                                                             (fun uu____6842 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____6868
                                                                    =
                                                                    let uu____6871
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6871
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6868
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
                                                                    let uu____6907
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6907)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____6924
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____6924
                                                                  with
                                                                  | (hd1,uu____6943)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6970)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6987
                                                                    -> false)
                                                                   in
                                                                let uu____6989
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
                                                                    let uu____7032
                                                                    = imp  in
                                                                    match uu____7032
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7043
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7043
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7065)
                                                                    ->
                                                                    let uu____7090
                                                                    =
                                                                    let uu____7091
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7091.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7090
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7099)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___987_7119
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___987_7119.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___987_7119.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___987_7119.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___987_7119.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7122
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7128
                                                                     ->
                                                                    let uu____7129
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7131
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7129
                                                                    uu____7131)
                                                                    (fun
                                                                    uu____7138
                                                                     ->
                                                                    let env =
                                                                    let uu___992_7140
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___992_7140.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7143
                                                                    =
                                                                    let uu____7146
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7150
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7152
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7150
                                                                    uu____7152
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7158
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7146
                                                                    uu____7158
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7143
                                                                    (fun
                                                                    uu____7162
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____6989
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
                                                                    let uu____7226
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7226
                                                                    then
                                                                    let uu____7231
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7231
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
                                                                    let uu____7246
                                                                    =
                                                                    let uu____7248
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7248
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7246)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7249
                                                                    =
                                                                    let uu____7252
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7252
                                                                    guard  in
                                                                    bind
                                                                    uu____7249
                                                                    (fun
                                                                    uu____7256
                                                                     ->
                                                                    let uu____7257
                                                                    =
                                                                    let uu____7260
                                                                    =
                                                                    let uu____7262
                                                                    =
                                                                    let uu____7264
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7265
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7264
                                                                    uu____7265
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7262
                                                                     in
                                                                    if
                                                                    uu____7260
                                                                    then
                                                                    let uu____7269
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7269
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7257
                                                                    (fun
                                                                    uu____7274
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6028  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6025
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7298 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7298 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7308::(e1,uu____7310)::(e2,uu____7312)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____7373 ->
        let uu____7376 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7376 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____7391 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____7391);
              (let uu____7394 = FStar_Syntax_Util.head_and_args t  in
               match uu____7394 with
               | (hd1,args) ->
                   let uu____7443 =
                     let uu____7458 =
                       let uu____7459 = FStar_Syntax_Subst.compress hd1  in
                       uu____7459.FStar_Syntax_Syntax.n  in
                     (uu____7458, args)  in
                   (match uu____7443 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____7479,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____7480))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____7545 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____7547 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____7545
                            uu____7547);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____7554 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7591 = destruct_eq' typ  in
    match uu____7591 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7621 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7621 with
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
        let uu____7690 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7690 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7748 = aux e'  in
               FStar_Util.map_opt uu____7748
                 (fun uu____7779  ->
                    match uu____7779 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7805 = aux e  in
      FStar_Util.map_opt uu____7805
        (fun uu____7836  ->
           match uu____7836 with
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
          let uu____7910 =
            let uu____7921 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____7921  in
          FStar_Util.map_opt uu____7910
            (fun uu____7939  ->
               match uu____7939 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1089_7961 = bv  in
                     let uu____7962 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1089_7961.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1089_7961.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7962
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1093_7970 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7971 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7980 =
                       let uu____7983 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7983  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1093_7970.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7971;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7980;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1093_7970.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1093_7970.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1093_7970.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1093_7970.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1096_7984 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1096_7984.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1096_7984.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1096_7984.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1096_7984.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7995 =
      let uu____7998 = cur_goal ()  in
      bind uu____7998
        (fun goal  ->
           let uu____8006 = h  in
           match uu____8006 with
           | (bv,uu____8010) ->
               mlog
                 (fun uu____8018  ->
                    let uu____8019 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8021 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8019
                      uu____8021)
                 (fun uu____8026  ->
                    let uu____8027 =
                      let uu____8038 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8038  in
                    match uu____8027 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8065 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8065 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8080 =
                               let uu____8081 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8081.FStar_Syntax_Syntax.n  in
                             (match uu____8080 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1119_8098 = bv2  in
                                    let uu____8099 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1119_8098.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1119_8098.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8099
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1123_8107 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8108 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8117 =
                                      let uu____8120 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8120
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1123_8107.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8108;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8117;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1123_8107.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1123_8107.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1123_8107.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1123_8107.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1126_8123 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1126_8123.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1126_8123.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1126_8123.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1126_8123.FStar_Tactics_Types.label)
                                     })
                              | uu____8124 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8126 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7995
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____8156 =
        let uu____8159 = cur_goal ()  in
        bind uu____8159
          (fun goal  ->
             let uu____8170 = b  in
             match uu____8170 with
             | (bv,uu____8174) ->
                 let bv' =
                   let uu____8180 =
                     let uu___1137_8181 = bv  in
                     let uu____8182 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8182;
                       FStar_Syntax_Syntax.index =
                         (uu___1137_8181.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1137_8181.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8180  in
                 let s1 =
                   let uu____8187 =
                     let uu____8188 =
                       let uu____8195 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8195)  in
                     FStar_Syntax_Syntax.NT uu____8188  in
                   [uu____8187]  in
                 let uu____8200 = subst_goal bv bv' s1 goal  in
                 (match uu____8200 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8156
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8222 =
      let uu____8225 = cur_goal ()  in
      bind uu____8225
        (fun goal  ->
           let uu____8234 = b  in
           match uu____8234 with
           | (bv,uu____8238) ->
               let uu____8243 =
                 let uu____8254 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8254  in
               (match uu____8243 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8281 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8281 with
                     | (ty,u) ->
                         let uu____8290 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8290
                           (fun uu____8309  ->
                              match uu____8309 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1161_8319 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1161_8319.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1161_8319.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8323 =
                                      let uu____8324 =
                                        let uu____8331 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8331)  in
                                      FStar_Syntax_Syntax.NT uu____8324  in
                                    [uu____8323]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1166_8343 = b1  in
                                         let uu____8344 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1166_8343.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1166_8343.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8344
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8351  ->
                                       let new_goal =
                                         let uu____8353 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8354 =
                                           let uu____8355 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8355
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8353 uu____8354
                                          in
                                       let uu____8356 = add_goals [new_goal]
                                          in
                                       bind uu____8356
                                         (fun uu____8361  ->
                                            let uu____8362 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8362
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8222
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8388 =
        let uu____8391 = cur_goal ()  in
        bind uu____8391
          (fun goal  ->
             let uu____8400 = b  in
             match uu____8400 with
             | (bv,uu____8404) ->
                 let uu____8409 =
                   let uu____8420 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8420  in
                 (match uu____8409 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8450 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8450
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1187_8455 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1187_8455.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1187_8455.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8457 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8457))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8388
  
let (revert : unit -> unit tac) =
  fun uu____8470  ->
    let uu____8473 = cur_goal ()  in
    bind uu____8473
      (fun goal  ->
         let uu____8479 =
           let uu____8486 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8486  in
         match uu____8479 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8503 =
                 let uu____8506 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8506  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8503
                in
             let uu____8521 = new_uvar "revert" env' typ'  in
             bind uu____8521
               (fun uu____8537  ->
                  match uu____8537 with
                  | (r,u_r) ->
                      let uu____8546 =
                        let uu____8549 =
                          let uu____8550 =
                            let uu____8551 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8551.FStar_Syntax_Syntax.pos  in
                          let uu____8554 =
                            let uu____8559 =
                              let uu____8560 =
                                let uu____8569 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8569  in
                              [uu____8560]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8559  in
                          uu____8554 FStar_Pervasives_Native.None uu____8550
                           in
                        set_solution goal uu____8549  in
                      bind uu____8546
                        (fun uu____8588  ->
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
      let uu____8602 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8602
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8618 = cur_goal ()  in
    bind uu____8618
      (fun goal  ->
         mlog
           (fun uu____8626  ->
              let uu____8627 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8629 =
                let uu____8631 =
                  let uu____8633 =
                    let uu____8642 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8642  in
                  FStar_All.pipe_right uu____8633 FStar_List.length  in
                FStar_All.pipe_right uu____8631 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8627 uu____8629)
           (fun uu____8663  ->
              let uu____8664 =
                let uu____8675 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8675  in
              match uu____8664 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8720 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8720
                        then
                          let uu____8725 =
                            let uu____8727 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8727
                             in
                          fail uu____8725
                        else check1 bvs2
                     in
                  let uu____8732 =
                    let uu____8734 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8734  in
                  if uu____8732
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8741 = check1 bvs  in
                     bind uu____8741
                       (fun uu____8747  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8749 =
                            let uu____8756 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8756  in
                          bind uu____8749
                            (fun uu____8766  ->
                               match uu____8766 with
                               | (ut,uvar_ut) ->
                                   let uu____8775 = set_solution goal ut  in
                                   bind uu____8775
                                     (fun uu____8780  ->
                                        let uu____8781 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8781))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8789  ->
    let uu____8792 = cur_goal ()  in
    bind uu____8792
      (fun goal  ->
         let uu____8798 =
           let uu____8805 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8805  in
         match uu____8798 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8814) ->
             let uu____8819 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8819)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8832 = cur_goal ()  in
    bind uu____8832
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8842 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8842  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8845  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____8858 = cur_goal ()  in
    bind uu____8858
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8868 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8868  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8871  -> add_goals [g']))
  
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
            let uu____8912 = FStar_Syntax_Subst.compress t  in
            uu____8912.FStar_Syntax_Syntax.n  in
          let uu____8915 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1371_8922 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1371_8922.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1371_8922.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____8915
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____8939 =
                   let uu____8940 = FStar_Syntax_Subst.compress t1  in
                   uu____8940.FStar_Syntax_Syntax.n  in
                 match uu____8939 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8971 = ff hd1  in
                     bind uu____8971
                       (fun hd2  ->
                          let fa uu____8997 =
                            match uu____8997 with
                            | (a,q) ->
                                let uu____9018 = ff a  in
                                bind uu____9018 (fun a1  -> ret (a1, q))
                             in
                          let uu____9037 = mapM fa args  in
                          bind uu____9037
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9119 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9119 with
                      | (bs1,t') ->
                          let uu____9128 =
                            let uu____9131 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9131 t'  in
                          bind uu____9128
                            (fun t''  ->
                               let uu____9135 =
                                 let uu____9136 =
                                   let uu____9155 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9164 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9155, uu____9164, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9136  in
                               ret uu____9135))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9239 = ff hd1  in
                     bind uu____9239
                       (fun hd2  ->
                          let ffb br =
                            let uu____9254 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9254 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9286 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9286  in
                                let uu____9287 = ff1 e  in
                                bind uu____9287
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9302 = mapM ffb brs  in
                          bind uu____9302
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9346;
                          FStar_Syntax_Syntax.lbtyp = uu____9347;
                          FStar_Syntax_Syntax.lbeff = uu____9348;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9350;
                          FStar_Syntax_Syntax.lbpos = uu____9351;_}::[]),e)
                     ->
                     let lb =
                       let uu____9379 =
                         let uu____9380 = FStar_Syntax_Subst.compress t1  in
                         uu____9380.FStar_Syntax_Syntax.n  in
                       match uu____9379 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9384) -> lb
                       | uu____9400 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9410 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9410
                         (fun def1  ->
                            ret
                              (let uu___1324_9416 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1324_9416.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1324_9416.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1324_9416.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1324_9416.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1324_9416.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1324_9416.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9417 = fflb lb  in
                     bind uu____9417
                       (fun lb1  ->
                          let uu____9427 =
                            let uu____9432 =
                              let uu____9433 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9433]  in
                            FStar_Syntax_Subst.open_term uu____9432 e  in
                          match uu____9427 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9463 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9463  in
                              let uu____9464 = ff1 e1  in
                              bind uu____9464
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9511 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9511
                         (fun def  ->
                            ret
                              (let uu___1342_9517 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1342_9517.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1342_9517.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1342_9517.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1342_9517.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1342_9517.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1342_9517.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9518 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9518 with
                      | (lbs1,e1) ->
                          let uu____9533 = mapM fflb lbs1  in
                          bind uu____9533
                            (fun lbs2  ->
                               let uu____9545 = ff e1  in
                               bind uu____9545
                                 (fun e2  ->
                                    let uu____9553 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9553 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9624 = ff t2  in
                     bind uu____9624
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9655 = ff t2  in
                     bind uu____9655
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9662 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1366_9669 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1366_9669.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1366_9669.FStar_Syntax_Syntax.vars)
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
              let uu____9716 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1379_9725 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1379_9725.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1379_9725.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1379_9725.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1379_9725.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1379_9725.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1379_9725.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1379_9725.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1379_9725.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1379_9725.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1379_9725.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1379_9725.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1379_9725.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1379_9725.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1379_9725.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1379_9725.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1379_9725.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1379_9725.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1379_9725.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1379_9725.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1379_9725.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1379_9725.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1379_9725.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1379_9725.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1379_9725.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1379_9725.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1379_9725.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1379_9725.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1379_9725.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1379_9725.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1379_9725.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1379_9725.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1379_9725.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1379_9725.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1379_9725.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1379_9725.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1379_9725.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1379_9725.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1379_9725.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1379_9725.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1379_9725.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1379_9725.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1379_9725.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9716 with
              | (t1,lcomp,g) ->
                  let uu____9732 =
                    (let uu____9736 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9736) ||
                      (let uu____9739 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9739)
                     in
                  if uu____9732
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9750 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9750
                         (fun uu____9767  ->
                            match uu____9767 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9780  ->
                                      let uu____9781 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9783 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9781 uu____9783);
                                 (let uu____9786 =
                                    let uu____9789 =
                                      let uu____9790 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9790 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9789
                                      opts label1
                                     in
                                  bind uu____9786
                                    (fun uu____9794  ->
                                       let uu____9795 =
                                         bind tau
                                           (fun uu____9801  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9807  ->
                                                   let uu____9808 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9810 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9808 uu____9810);
                                              ret ut1)
                                          in
                                       focus uu____9795))))
                        in
                     let uu____9813 = catch rewrite_eq  in
                     bind uu____9813
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
          let uu____10025 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10025
            (fun t1  ->
               let uu____10033 =
                 f env
                   (let uu___1456_10041 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1456_10041.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1456_10041.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10033
                 (fun uu____10057  ->
                    match uu____10057 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10080 =
                               let uu____10081 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10081.FStar_Syntax_Syntax.n  in
                             match uu____10080 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10118 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10118
                                   (fun uu____10140  ->
                                      match uu____10140 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10156 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10156
                                            (fun uu____10180  ->
                                               match uu____10180 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1436_10210 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1436_10210.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1436_10210.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10252 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10252 with
                                  | (bs1,t') ->
                                      let uu____10267 =
                                        let uu____10274 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10274 ctrl1 t'
                                         in
                                      bind uu____10267
                                        (fun uu____10289  ->
                                           match uu____10289 with
                                           | (t'',ctrl2) ->
                                               let uu____10304 =
                                                 let uu____10311 =
                                                   let uu___1449_10314 = t4
                                                      in
                                                   let uu____10317 =
                                                     let uu____10318 =
                                                       let uu____10337 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10346 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10337,
                                                         uu____10346, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10318
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10317;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1449_10314.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1449_10314.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10311, ctrl2)  in
                                               ret uu____10304))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10399 -> ret (t3, ctrl1))))

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
              let uu____10445 = ctrl_tac_fold f env ctrl t  in
              bind uu____10445
                (fun uu____10466  ->
                   match uu____10466 with
                   | (t1,ctrl1) ->
                       let uu____10481 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10481
                         (fun uu____10505  ->
                            match uu____10505 with
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
                let uu____10596 =
                  let uu____10604 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10604
                    (fun uu____10615  ->
                       let uu____10616 = ctrl t1  in
                       bind uu____10616
                         (fun res  ->
                            let uu____10642 = trivial ()  in
                            bind uu____10642 (fun uu____10651  -> ret res)))
                   in
                bind uu____10596
                  (fun uu____10669  ->
                     match uu____10669 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10698 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1486_10707 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1486_10707.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1486_10707.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1486_10707.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1486_10707.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1486_10707.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1486_10707.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1486_10707.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1486_10707.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1486_10707.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1486_10707.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1486_10707.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1486_10707.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1486_10707.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1486_10707.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1486_10707.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1486_10707.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1486_10707.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1486_10707.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1486_10707.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1486_10707.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1486_10707.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1486_10707.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1486_10707.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1486_10707.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1486_10707.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1486_10707.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1486_10707.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1486_10707.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1486_10707.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1486_10707.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1486_10707.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1486_10707.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1486_10707.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1486_10707.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1486_10707.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1486_10707.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1486_10707.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1486_10707.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1486_10707.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1486_10707.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1486_10707.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1486_10707.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10698 with
                            | (t2,lcomp,g) ->
                                let uu____10718 =
                                  (let uu____10722 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10722) ||
                                    (let uu____10725 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10725)
                                   in
                                if uu____10718
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10741 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10741
                                     (fun uu____10762  ->
                                        match uu____10762 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10779  ->
                                                  let uu____10780 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10782 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10780 uu____10782);
                                             (let uu____10785 =
                                                let uu____10788 =
                                                  let uu____10789 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10789 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10788 opts label1
                                                 in
                                              bind uu____10785
                                                (fun uu____10797  ->
                                                   let uu____10798 =
                                                     bind rewriter
                                                       (fun uu____10812  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10818 
                                                               ->
                                                               let uu____10819
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10821
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10819
                                                                 uu____10821);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10798)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____10866 =
        bind get
          (fun ps  ->
             let uu____10876 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10876 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10914  ->
                       let uu____10915 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10915);
                  bind dismiss_all
                    (fun uu____10920  ->
                       let uu____10921 =
                         let uu____10928 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10928
                           keepGoing gt1
                          in
                       bind uu____10921
                         (fun uu____10938  ->
                            match uu____10938 with
                            | (gt',uu____10946) ->
                                (log ps
                                   (fun uu____10950  ->
                                      let uu____10951 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10951);
                                 (let uu____10954 = push_goals gs  in
                                  bind uu____10954
                                    (fun uu____10959  ->
                                       let uu____10960 =
                                         let uu____10963 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10963]  in
                                       add_goals uu____10960)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10866
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10988 =
        bind get
          (fun ps  ->
             let uu____10998 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10998 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11036  ->
                       let uu____11037 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11037);
                  bind dismiss_all
                    (fun uu____11042  ->
                       let uu____11043 =
                         let uu____11046 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11046 gt1
                          in
                       bind uu____11043
                         (fun gt'  ->
                            log ps
                              (fun uu____11054  ->
                                 let uu____11055 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11055);
                            (let uu____11058 = push_goals gs  in
                             bind uu____11058
                               (fun uu____11063  ->
                                  let uu____11064 =
                                    let uu____11067 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11067]  in
                                  add_goals uu____11064))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10988
  
let (trefl : unit -> unit tac) =
  fun uu____11080  ->
    let uu____11083 =
      let uu____11086 = cur_goal ()  in
      bind uu____11086
        (fun g  ->
           let uu____11104 =
             let uu____11109 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____11109  in
           match uu____11104 with
           | FStar_Pervasives_Native.Some t ->
               let uu____11117 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____11117 with
                | (hd1,args) ->
                    let uu____11156 =
                      let uu____11169 =
                        let uu____11170 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____11170.FStar_Syntax_Syntax.n  in
                      (uu____11169, args)  in
                    (match uu____11156 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____11184::(l,uu____11186)::(r,uu____11188)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____11235 =
                           let uu____11239 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____11239 l r  in
                         bind uu____11235
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____11250 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11250 l
                                    in
                                 let r1 =
                                   let uu____11252 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11252 r
                                    in
                                 let uu____11253 =
                                   let uu____11257 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____11257 l1 r1  in
                                 bind uu____11253
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____11267 =
                                           let uu____11269 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11269 l1  in
                                         let uu____11270 =
                                           let uu____11272 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11272 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____11267 uu____11270))))
                     | (hd2,uu____11275) ->
                         let uu____11292 =
                           let uu____11294 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____11294 t  in
                         fail1 "trefl: not an equality (%s)" uu____11292))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11083
  
let (dup : unit -> unit tac) =
  fun uu____11311  ->
    let uu____11314 = cur_goal ()  in
    bind uu____11314
      (fun g  ->
         let uu____11320 =
           let uu____11327 = FStar_Tactics_Types.goal_env g  in
           let uu____11328 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11327 uu____11328  in
         bind uu____11320
           (fun uu____11338  ->
              match uu____11338 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1578_11348 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1578_11348.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1578_11348.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1578_11348.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1578_11348.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11351  ->
                       let uu____11352 =
                         let uu____11355 = FStar_Tactics_Types.goal_env g  in
                         let uu____11356 =
                           let uu____11357 =
                             let uu____11358 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11359 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11358
                               uu____11359
                              in
                           let uu____11360 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11361 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11357 uu____11360 u
                             uu____11361
                            in
                         add_irrelevant_goal "dup equation" uu____11355
                           uu____11356 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11352
                         (fun uu____11365  ->
                            let uu____11366 = add_goals [g']  in
                            bind uu____11366 (fun uu____11370  -> ret ())))))
  
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
              let uu____11496 = f x y  in
              if uu____11496 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11519 -> (acc, l11, l21)  in
        let uu____11534 = aux [] l1 l2  in
        match uu____11534 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11640 = get_phi g1  in
      match uu____11640 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11647 = get_phi g2  in
          (match uu____11647 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11660 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11660 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11691 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11691 phi1  in
                    let t2 =
                      let uu____11701 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11701 phi2  in
                    let uu____11710 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11710
                      (fun uu____11715  ->
                         let uu____11716 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11716
                           (fun uu____11723  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1629_11728 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11729 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1629_11728.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1629_11728.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1629_11728.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1629_11728.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11729;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1629_11728.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1629_11728.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1629_11728.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1629_11728.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1629_11728.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1629_11728.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1629_11728.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1629_11728.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1629_11728.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1629_11728.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1629_11728.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1629_11728.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1629_11728.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1629_11728.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1629_11728.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1629_11728.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1629_11728.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1629_11728.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1629_11728.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1629_11728.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1629_11728.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1629_11728.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1629_11728.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1629_11728.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1629_11728.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1629_11728.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1629_11728.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1629_11728.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1629_11728.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1629_11728.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1629_11728.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1629_11728.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1629_11728.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1629_11728.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1629_11728.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1629_11728.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1629_11728.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11733 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11733
                                (fun goal  ->
                                   mlog
                                     (fun uu____11743  ->
                                        let uu____11744 =
                                          goal_to_string_verbose g1  in
                                        let uu____11746 =
                                          goal_to_string_verbose g2  in
                                        let uu____11748 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11744 uu____11746 uu____11748)
                                     (fun uu____11752  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11760  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11776 =
               set
                 (let uu___1644_11781 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1644_11781.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1644_11781.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1644_11781.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1644_11781.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1644_11781.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1644_11781.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1644_11781.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1644_11781.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1644_11781.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1644_11781.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1644_11781.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1644_11781.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11776
               (fun uu____11784  ->
                  let uu____11785 = join_goals g1 g2  in
                  bind uu____11785 (fun g12  -> add_goals [g12]))
         | uu____11790 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11806 =
      let uu____11809 = cur_goal ()  in
      bind uu____11809
        (fun g  ->
           FStar_Options.push ();
           (let uu____11822 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11822);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1655_11829 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1655_11829.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1655_11829.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1655_11829.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1655_11829.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11806
  
let (top_env : unit -> env tac) =
  fun uu____11846  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11861  ->
    let uu____11865 = cur_goal ()  in
    bind uu____11865
      (fun g  ->
         let uu____11872 =
           (FStar_Options.lax ()) ||
             (let uu____11875 = FStar_Tactics_Types.goal_env g  in
              uu____11875.FStar_TypeChecker_Env.lax)
            in
         ret uu____11872)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11892 =
        mlog
          (fun uu____11897  ->
             let uu____11898 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11898)
          (fun uu____11903  ->
             let uu____11904 = cur_goal ()  in
             bind uu____11904
               (fun goal  ->
                  let env =
                    let uu____11912 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11912 ty  in
                  let uu____11913 = __tc_ghost env tm  in
                  bind uu____11913
                    (fun uu____11932  ->
                       match uu____11932 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11946  ->
                                let uu____11947 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11947)
                             (fun uu____11951  ->
                                mlog
                                  (fun uu____11954  ->
                                     let uu____11955 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11955)
                                  (fun uu____11960  ->
                                     let uu____11961 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11961
                                       (fun uu____11966  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11892
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11991 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11997 =
              let uu____12004 =
                let uu____12005 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12005
                 in
              new_uvar "uvar_env.2" env uu____12004  in
            bind uu____11997
              (fun uu____12022  ->
                 match uu____12022 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11991
        (fun typ  ->
           let uu____12034 = new_uvar "uvar_env" env typ  in
           bind uu____12034
             (fun uu____12049  ->
                match uu____12049 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12068 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12087 -> g.FStar_Tactics_Types.opts
             | uu____12090 -> FStar_Options.peek ()  in
           let uu____12093 = FStar_Syntax_Util.head_and_args t  in
           match uu____12093 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12113);
                FStar_Syntax_Syntax.pos = uu____12114;
                FStar_Syntax_Syntax.vars = uu____12115;_},uu____12116)
               ->
               let env1 =
                 let uu___1709_12158 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1709_12158.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1709_12158.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1709_12158.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1709_12158.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1709_12158.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1709_12158.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1709_12158.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1709_12158.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1709_12158.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1709_12158.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1709_12158.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1709_12158.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1709_12158.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1709_12158.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1709_12158.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1709_12158.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1709_12158.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1709_12158.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1709_12158.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1709_12158.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1709_12158.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1709_12158.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1709_12158.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1709_12158.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1709_12158.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1709_12158.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1709_12158.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1709_12158.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1709_12158.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1709_12158.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1709_12158.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1709_12158.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1709_12158.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1709_12158.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1709_12158.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1709_12158.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1709_12158.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1709_12158.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1709_12158.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1709_12158.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1709_12158.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1709_12158.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12162 =
                 let uu____12165 = bnorm_goal g  in [uu____12165]  in
               add_goals uu____12162
           | uu____12166 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12068
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12228 = if b then t2 else ret false  in
             bind uu____12228 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12254 = trytac comp  in
      bind uu____12254
        (fun uu___4_12266  ->
           match uu___4_12266 with
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
        let uu____12308 =
          bind get
            (fun ps  ->
               let uu____12316 = __tc e t1  in
               bind uu____12316
                 (fun uu____12337  ->
                    match uu____12337 with
                    | (t11,ty1,g1) ->
                        let uu____12350 = __tc e t2  in
                        bind uu____12350
                          (fun uu____12371  ->
                             match uu____12371 with
                             | (t21,ty2,g2) ->
                                 let uu____12384 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12384
                                   (fun uu____12391  ->
                                      let uu____12392 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12392
                                        (fun uu____12400  ->
                                           let uu____12401 =
                                             do_unify e ty1 ty2  in
                                           let uu____12405 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12401 uu____12405)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12308
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12453  ->
             let uu____12454 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12454
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
        (fun uu____12488  ->
           let uu____12489 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12489)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12500 =
      mlog
        (fun uu____12505  ->
           let uu____12506 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12506)
        (fun uu____12511  ->
           let uu____12512 = cur_goal ()  in
           bind uu____12512
             (fun g  ->
                let uu____12518 =
                  let uu____12527 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12527 ty  in
                bind uu____12518
                  (fun uu____12539  ->
                     match uu____12539 with
                     | (ty1,uu____12549,guard) ->
                         let uu____12551 =
                           let uu____12554 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12554 guard  in
                         bind uu____12551
                           (fun uu____12558  ->
                              let uu____12559 =
                                let uu____12563 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12564 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12563 uu____12564 ty1  in
                              bind uu____12559
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12573 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12573
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12580 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12581 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12580
                                          uu____12581
                                         in
                                      let nty =
                                        let uu____12583 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12583 ty1  in
                                      let uu____12584 =
                                        let uu____12588 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12588 ng nty  in
                                      bind uu____12584
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12597 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12597
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12500
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12671 =
      let uu____12680 = cur_goal ()  in
      bind uu____12680
        (fun g  ->
           let uu____12692 =
             let uu____12701 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12701 s_tm  in
           bind uu____12692
             (fun uu____12719  ->
                match uu____12719 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12737 =
                      let uu____12740 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12740 guard  in
                    bind uu____12737
                      (fun uu____12753  ->
                         let uu____12754 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12754 with
                         | (h,args) ->
                             let uu____12799 =
                               let uu____12806 =
                                 let uu____12807 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12807.FStar_Syntax_Syntax.n  in
                               match uu____12806 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12822;
                                      FStar_Syntax_Syntax.vars = uu____12823;_},us)
                                   -> ret (fv, us)
                               | uu____12833 -> fail "type is not an fv"  in
                             bind uu____12799
                               (fun uu____12854  ->
                                  match uu____12854 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12870 =
                                        let uu____12873 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12873 t_lid
                                         in
                                      (match uu____12870 with
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
                                                  (fun uu____12924  ->
                                                     let uu____12925 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12925 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12940 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12968
                                                                  =
                                                                  let uu____12971
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12971
                                                                    c_lid
                                                                   in
                                                                match uu____12968
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
                                                                    uu____13045
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
                                                                    let uu____13050
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13050
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13073
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13073
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13116
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____13116
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____13189
                                                                    =
                                                                    let uu____13191
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____13191
                                                                     in
                                                                    failwhen
                                                                    uu____13189
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13210
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
                                                                    uu___5_13227
                                                                    =
                                                                    match uu___5_13227
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13231)
                                                                    -> true
                                                                    | 
                                                                    uu____13234
                                                                    -> false
                                                                     in
                                                                    let uu____13238
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13238
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
                                                                    uu____13372
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
                                                                    uu____13434
                                                                     ->
                                                                    match uu____13434
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13454),
                                                                    (t,uu____13456))
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
                                                                    uu____13526
                                                                     ->
                                                                    match uu____13526
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13553),
                                                                    (t,uu____13555))
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
                                                                    uu____13614
                                                                     ->
                                                                    match uu____13614
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
                                                                    let uu____13669
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1873_13686
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1873_13686.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13669
                                                                    with
                                                                    | 
                                                                    (uu____13700,uu____13701,uu____13702,pat_t,uu____13704,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13711
                                                                    =
                                                                    let uu____13712
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13712
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13711
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13717
                                                                    =
                                                                    let uu____13726
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13726]
                                                                     in
                                                                    let uu____13745
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13717
                                                                    uu____13745
                                                                     in
                                                                    let nty =
                                                                    let uu____13751
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13751
                                                                     in
                                                                    let uu____13754
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13754
                                                                    (fun
                                                                    uu____13784
                                                                     ->
                                                                    match uu____13784
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
                                                                    let uu____13811
                                                                    =
                                                                    let uu____13822
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13822]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13811
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13858
                                                                    =
                                                                    let uu____13869
                                                                    =
                                                                    let uu____13874
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13874)
                                                                     in
                                                                    (g', br,
                                                                    uu____13869)
                                                                     in
                                                                    ret
                                                                    uu____13858))))))
                                                                    | 
                                                                    uu____13895
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12940
                                                           (fun goal_brs  ->
                                                              let uu____13945
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13945
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
                                                                  let uu____14018
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____14018
                                                                    (
                                                                    fun
                                                                    uu____14029
                                                                     ->
                                                                    let uu____14030
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14030
                                                                    (fun
                                                                    uu____14040
                                                                     ->
                                                                    ret infos))))
                                            | uu____14047 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12671
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14096::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14126 = init xs  in x :: uu____14126
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14139 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14148) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14214 = last args  in
          (match uu____14214 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14244 =
                 let uu____14245 =
                   let uu____14250 =
                     let uu____14251 =
                       let uu____14256 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14256  in
                     uu____14251 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14250, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14245  in
               FStar_All.pipe_left ret uu____14244)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14267,uu____14268) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14321 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14321 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14363 =
                      let uu____14364 =
                        let uu____14369 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14369)  in
                      FStar_Reflection_Data.Tv_Abs uu____14364  in
                    FStar_All.pipe_left ret uu____14363))
      | FStar_Syntax_Syntax.Tm_type uu____14372 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14397 ->
          let uu____14412 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14412 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14443 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14443 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14496 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14509 =
            let uu____14510 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14510  in
          FStar_All.pipe_left ret uu____14509
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14531 =
            let uu____14532 =
              let uu____14537 =
                let uu____14538 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14538  in
              (uu____14537, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14532  in
          FStar_All.pipe_left ret uu____14531
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14578 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14583 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14583 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14636 ->
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
             | FStar_Util.Inr uu____14678 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14682 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14682 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14702 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14708 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14763 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14763
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14784 =
                  let uu____14791 =
                    FStar_List.map
                      (fun uu____14804  ->
                         match uu____14804 with
                         | (p1,uu____14813) -> inspect_pat p1) ps
                     in
                  (fv, uu____14791)  in
                FStar_Reflection_Data.Pat_Cons uu____14784
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
              (fun uu___6_14909  ->
                 match uu___6_14909 with
                 | (pat,uu____14931,t5) ->
                     let uu____14949 = inspect_pat pat  in (uu____14949, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14958 ->
          ((let uu____14960 =
              let uu____14966 =
                let uu____14968 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14970 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14968 uu____14970
                 in
              (FStar_Errors.Warning_CantInspect, uu____14966)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14960);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14139
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14988 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14988
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14992 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14992
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14996 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14996
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15003 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15003
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15028 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15028
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15045 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15045
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15064 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15064
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15068 =
          let uu____15069 =
            let uu____15076 =
              let uu____15077 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15077  in
            FStar_Syntax_Syntax.mk uu____15076  in
          uu____15069 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15068
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15082 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15082
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15093 =
          let uu____15094 =
            let uu____15101 =
              let uu____15102 =
                let uu____15116 =
                  let uu____15119 =
                    let uu____15120 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15120]  in
                  FStar_Syntax_Subst.close uu____15119 t2  in
                ((false, [lb]), uu____15116)  in
              FStar_Syntax_Syntax.Tm_let uu____15102  in
            FStar_Syntax_Syntax.mk uu____15101  in
          uu____15094 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15093
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15162 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15162 with
         | (lbs,body) ->
             let uu____15177 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15177)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15214 =
                let uu____15215 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15215  in
              FStar_All.pipe_left wrap uu____15214
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15222 =
                let uu____15223 =
                  let uu____15237 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15255 = pack_pat p1  in
                         (uu____15255, false)) ps
                     in
                  (fv, uu____15237)  in
                FStar_Syntax_Syntax.Pat_cons uu____15223  in
              FStar_All.pipe_left wrap uu____15222
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
            (fun uu___7_15304  ->
               match uu___7_15304 with
               | (pat,t1) ->
                   let uu____15321 = pack_pat pat  in
                   (uu____15321, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15369 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15369
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15397 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15397
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15443 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15443
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15482 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15482
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15502 =
        bind get
          (fun ps  ->
             let uu____15508 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15508 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15502
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15542 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2171_15549 = ps  in
                 let uu____15550 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2171_15549.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2171_15549.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2171_15549.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2171_15549.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2171_15549.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2171_15549.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2171_15549.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2171_15549.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2171_15549.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2171_15549.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2171_15549.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2171_15549.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15550
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15542
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15577 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15577 with
      | (u,ctx_uvars,g_u) ->
          let uu____15610 = FStar_List.hd ctx_uvars  in
          (match uu____15610 with
           | (ctx_uvar,uu____15624) ->
               let g =
                 let uu____15626 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15626 false
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
        let uu____15649 = goal_of_goal_ty env typ  in
        match uu____15649 with
        | (g,g_u) ->
            let ps =
              let uu____15661 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15664 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15661;
                FStar_Tactics_Types.local_state = uu____15664
              }  in
            let uu____15674 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15674)
  