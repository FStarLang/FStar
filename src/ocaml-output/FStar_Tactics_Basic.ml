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
            let uu____558 = FStar_Syntax_Subst.subst_binders subst1 [b]  in
            (match uu____558 with
             | b1::[] ->
                 let uu____602 = b1  in
                 (match uu____602 with
                  | (bv0,q) ->
                      let nbs =
                        fresh_until (s bv0)
                          (fun s1  ->
                             Prims.op_Negation (FStar_List.mem s1 seen))
                         in
                      let bv = sset bv0 nbs  in
                      let b2 = (bv, q)  in
                      let uu____643 =
                        let uu____646 =
                          let uu____649 =
                            let uu____650 =
                              let uu____657 =
                                FStar_Syntax_Syntax.bv_to_name bv  in
                              (bv0, uu____657)  in
                            FStar_Syntax_Syntax.NT uu____650  in
                          [uu____649]  in
                        FStar_List.append subst1 uu____646  in
                      go (nbs :: seen) uu____643 bs2 (b2 :: bs') t1))
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
            let uu____719 = FStar_Options.print_implicits ()  in
            if uu____719
            then
              let uu____723 = FStar_Tactics_Types.goal_env g  in
              let uu____724 = FStar_Tactics_Types.goal_witness g  in
              tts uu____723 uu____724
            else
              (let uu____727 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____727 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____733 = FStar_Tactics_Types.goal_env g  in
                   let uu____734 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____733 uu____734)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____757 = FStar_Util.string_of_int i  in
                let uu____759 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____757 uu____759
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
          let uu____783 = unshadow goal_binders goal_ty  in
          match uu____783 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____797 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____800 =
                     let uu____802 = FStar_Tactics_Types.goal_env g  in
                     tts uu____802 goal_ty1  in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____797 w uu____800)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____829 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____829
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____854 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____854
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____886 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____886
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____899 =
      let uu____900 = FStar_Tactics_Types.goal_env g  in
      let uu____901 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____900 uu____901  in
    FStar_Syntax_Util.un_squash uu____899
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____910 = get_phi g  in FStar_Option.isSome uu____910 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____934  ->
    bind get
      (fun ps  ->
         let uu____942 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____942)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____957  ->
    match uu____957 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____979 =
          let uu____983 =
            let uu____987 =
              let uu____989 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____989
                msg
               in
            let uu____992 =
              let uu____996 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____1000 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____1000
                else ""  in
              let uu____1006 =
                let uu____1010 =
                  let uu____1012 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____1012
                  then
                    let uu____1017 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____1017
                  else ""  in
                [uu____1010]  in
              uu____996 :: uu____1006  in
            uu____987 :: uu____992  in
          let uu____1027 =
            let uu____1031 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____1051 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____1031 uu____1051  in
          FStar_List.append uu____983 uu____1027  in
        FStar_String.concat "" uu____979
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____1090 = unshadow g_binders g_type  in
    match uu____1090 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____1098 =
            let uu____1099 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____1099  in
          FStar_Syntax_Print.binders_to_json uu____1098 g_binders1  in
        let uu____1100 =
          let uu____1108 =
            let uu____1116 =
              let uu____1122 =
                let uu____1123 =
                  let uu____1131 =
                    let uu____1137 =
                      let uu____1138 =
                        let uu____1140 = FStar_Tactics_Types.goal_env g  in
                        let uu____1141 = FStar_Tactics_Types.goal_witness g
                           in
                        tts uu____1140 uu____1141  in
                      FStar_Util.JsonStr uu____1138  in
                    ("witness", uu____1137)  in
                  let uu____1144 =
                    let uu____1152 =
                      let uu____1158 =
                        let uu____1159 =
                          let uu____1161 = FStar_Tactics_Types.goal_env g  in
                          tts uu____1161 g_type1  in
                        FStar_Util.JsonStr uu____1159  in
                      ("type", uu____1158)  in
                    [uu____1152;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____1131 :: uu____1144  in
                FStar_Util.JsonAssoc uu____1123  in
              ("goal", uu____1122)  in
            [uu____1116]  in
          ("hyps", j_binders) :: uu____1108  in
        FStar_Util.JsonAssoc uu____1100
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____1215  ->
    match uu____1215 with
    | (msg,ps) ->
        let uu____1225 =
          let uu____1233 =
            let uu____1241 =
              let uu____1249 =
                let uu____1257 =
                  let uu____1263 =
                    let uu____1264 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____1264  in
                  ("goals", uu____1263)  in
                let uu____1269 =
                  let uu____1277 =
                    let uu____1283 =
                      let uu____1284 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____1284  in
                    ("smt-goals", uu____1283)  in
                  [uu____1277]  in
                uu____1257 :: uu____1269  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____1249
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____1241  in
          let uu____1318 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____1334 =
                let uu____1340 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____1340)  in
              [uu____1334]
            else []  in
          FStar_List.append uu____1233 uu____1318  in
        FStar_Util.JsonAssoc uu____1225
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1380  ->
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
         (let uu____1411 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____1411 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1484 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1484
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1498 . Prims.string -> Prims.string -> 'Auu____1498 tac =
  fun msg  ->
    fun x  -> let uu____1515 = FStar_Util.format1 msg x  in fail uu____1515
  
let fail2 :
  'Auu____1526 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1526 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1550 = FStar_Util.format2 msg x y  in fail uu____1550
  
let fail3 :
  'Auu____1563 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1563 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1594 = FStar_Util.format3 msg x y z  in fail uu____1594
  
let fail4 :
  'Auu____1609 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1609 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1647 = FStar_Util.format4 msg x y z w  in
            fail uu____1647
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1682 = run t ps  in
         match uu____1682 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___227_1706 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___227_1706.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___227_1706.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___227_1706.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___227_1706.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___227_1706.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___227_1706.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___227_1706.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___227_1706.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___227_1706.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___227_1706.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___227_1706.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___227_1706.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1745 = run t ps  in
         match uu____1745 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1793 = catch t  in
    bind uu____1793
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1820 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___253_1852  ->
              match () with
              | () -> let uu____1857 = trytac t  in run uu____1857 ps) ()
         with
         | FStar_Errors.Err (uu____1873,msg) ->
             (log ps
                (fun uu____1879  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1885,msg,uu____1887) ->
             (log ps
                (fun uu____1892  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1929 = run t ps  in
           match uu____1929 with
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
  fun p  -> mk_tac (fun uu____1953  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___288_1968 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___288_1968.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___288_1968.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___288_1968.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___288_1968.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___288_1968.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___288_1968.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___288_1968.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___288_1968.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___288_1968.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___288_1968.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___288_1968.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___288_1968.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1992 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1992
         then
           let uu____1996 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1998 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1996
             uu____1998
         else ());
        (try
           (fun uu___296_2009  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____2017 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2017
                    then
                      let uu____2021 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____2023 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____2025 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____2021
                        uu____2023 uu____2025
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____2036 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____2036 (fun uu____2041  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____2051,msg) ->
             mlog
               (fun uu____2057  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____2060  -> ret false)
         | FStar_Errors.Error (uu____2063,msg,r) ->
             mlog
               (fun uu____2071  ->
                  let uu____2072 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____2072) (fun uu____2076  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___322_2090 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___322_2090.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___322_2090.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___322_2090.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___326_2093 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___326_2093.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___326_2093.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___326_2093.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___326_2093.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___326_2093.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___326_2093.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___326_2093.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___326_2093.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___326_2093.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___326_2093.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___326_2093.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___326_2093.FStar_Tactics_Types.local_state)
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
          (fun uu____2120  ->
             (let uu____2122 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____2122
              then
                (FStar_Options.push ();
                 (let uu____2127 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____2131 = __do_unify env t1 t2  in
              bind uu____2131
                (fun r  ->
                   (let uu____2142 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2142 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___341_2156 = ps  in
         let uu____2157 =
           FStar_List.filter
             (fun g  ->
                let uu____2163 = check_goal_solved g  in
                FStar_Option.isNone uu____2163) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___341_2156.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___341_2156.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___341_2156.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2157;
           FStar_Tactics_Types.smt_goals =
             (uu___341_2156.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___341_2156.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___341_2156.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___341_2156.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___341_2156.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___341_2156.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___341_2156.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___341_2156.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___341_2156.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2181 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____2181 with
      | FStar_Pervasives_Native.Some uu____2186 ->
          let uu____2187 =
            let uu____2189 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____2189  in
          fail uu____2187
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____2210 = FStar_Tactics_Types.goal_env goal  in
      let uu____2211 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____2210 solution uu____2211
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____2218 =
         let uu___354_2219 = p  in
         let uu____2220 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_2219.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___354_2219.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___354_2219.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2220;
           FStar_Tactics_Types.smt_goals =
             (uu___354_2219.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_2219.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_2219.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_2219.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_2219.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_2219.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_2219.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_2219.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___354_2219.FStar_Tactics_Types.local_state)
         }  in
       set uu____2218)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____2242  ->
           let uu____2243 =
             let uu____2245 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____2245  in
           let uu____2246 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____2243 uu____2246)
        (fun uu____2251  ->
           let uu____2252 = trysolve goal solution  in
           bind uu____2252
             (fun b  ->
                if b
                then bind __dismiss (fun uu____2264  -> remove_solved_goals)
                else
                  (let uu____2267 =
                     let uu____2269 =
                       let uu____2271 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____2271 solution  in
                     let uu____2272 =
                       let uu____2274 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2275 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____2274 uu____2275  in
                     let uu____2276 =
                       let uu____2278 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2279 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____2278 uu____2279  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____2269 uu____2272 uu____2276
                      in
                   fail uu____2267)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2296 = set_solution goal solution  in
      bind uu____2296
        (fun uu____2300  ->
           bind __dismiss (fun uu____2302  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___370_2321 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_2321.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_2321.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_2321.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___370_2321.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_2321.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_2321.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_2321.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_2321.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_2321.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_2321.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_2321.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_2321.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___374_2340 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_2340.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_2340.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___374_2340.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___374_2340.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___374_2340.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_2340.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_2340.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_2340.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___374_2340.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___374_2340.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_2340.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_2340.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2356 = FStar_Options.defensive ()  in
    if uu____2356
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2366 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2366)
         in
      let b2 =
        b1 &&
          (let uu____2370 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2370)
         in
      let rec aux b3 e =
        let uu____2385 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2385 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2405 =
        (let uu____2409 = aux b2 env  in Prims.op_Negation uu____2409) &&
          (let uu____2412 = FStar_ST.op_Bang nwarn  in
           uu____2412 < (Prims.parse_int "5"))
         in
      (if uu____2405
       then
         ((let uu____2438 =
             let uu____2439 = FStar_Tactics_Types.goal_type g  in
             uu____2439.FStar_Syntax_Syntax.pos  in
           let uu____2442 =
             let uu____2448 =
               let uu____2450 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2450
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2448)  in
           FStar_Errors.log_issue uu____2438 uu____2442);
          (let uu____2454 =
             let uu____2456 = FStar_ST.op_Bang nwarn  in
             uu____2456 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____2454))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___396_2525 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___396_2525.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___396_2525.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___396_2525.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___396_2525.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___396_2525.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___396_2525.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___396_2525.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___396_2525.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___396_2525.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___396_2525.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___396_2525.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___396_2525.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___401_2546 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___401_2546.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___401_2546.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___401_2546.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___401_2546.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___401_2546.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___401_2546.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___401_2546.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___401_2546.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___401_2546.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___401_2546.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___401_2546.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___401_2546.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___406_2567 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___406_2567.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___406_2567.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___406_2567.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___406_2567.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___406_2567.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___406_2567.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___406_2567.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___406_2567.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___406_2567.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___406_2567.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___406_2567.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___406_2567.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___411_2588 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___411_2588.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___411_2588.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___411_2588.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___411_2588.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___411_2588.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___411_2588.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___411_2588.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___411_2588.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___411_2588.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___411_2588.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___411_2588.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___411_2588.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2600  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2631 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2631 with
        | (u,ctx_uvar,g_u) ->
            let uu____2669 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2669
              (fun uu____2678  ->
                 let uu____2679 =
                   let uu____2684 =
                     let uu____2685 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2685  in
                   (u, uu____2684)  in
                 ret uu____2679)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2706 = FStar_Syntax_Util.un_squash t1  in
    match uu____2706 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2718 =
          let uu____2719 = FStar_Syntax_Subst.compress t'1  in
          uu____2719.FStar_Syntax_Syntax.n  in
        (match uu____2718 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2724 -> false)
    | uu____2726 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2739 = FStar_Syntax_Util.un_squash t  in
    match uu____2739 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2750 =
          let uu____2751 = FStar_Syntax_Subst.compress t'  in
          uu____2751.FStar_Syntax_Syntax.n  in
        (match uu____2750 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2756 -> false)
    | uu____2758 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2771  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2783 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2783 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2790 = goal_to_string_verbose hd1  in
                    let uu____2792 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2790 uu____2792);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2805 =
      bind get
        (fun ps  ->
           let uu____2811 = cur_goal ()  in
           bind uu____2811
             (fun g  ->
                (let uu____2818 =
                   let uu____2819 = FStar_Tactics_Types.goal_type g  in
                   uu____2819.FStar_Syntax_Syntax.pos  in
                 let uu____2822 =
                   let uu____2828 =
                     let uu____2830 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2830
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2828)  in
                 FStar_Errors.log_issue uu____2818 uu____2822);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2805
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2853  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___456_2864 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___456_2864.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___456_2864.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___456_2864.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___456_2864.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___456_2864.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___456_2864.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___456_2864.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___456_2864.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___456_2864.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___456_2864.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___456_2864.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___456_2864.FStar_Tactics_Types.local_state)
           }  in
         let uu____2866 = set ps1  in
         bind uu____2866
           (fun uu____2871  ->
              let uu____2872 = FStar_BigInt.of_int_fs n1  in ret uu____2872))
  
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
              let uu____2910 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2910 phi  in
            let uu____2911 = new_uvar reason env typ  in
            bind uu____2911
              (fun uu____2926  ->
                 match uu____2926 with
                 | (uu____2933,ctx_uvar) ->
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
             (fun uu____2980  ->
                let uu____2981 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2981)
             (fun uu____2986  ->
                let e1 =
                  let uu___474_2988 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___474_2988.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___474_2988.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___474_2988.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___474_2988.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___474_2988.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___474_2988.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___474_2988.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___474_2988.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___474_2988.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___474_2988.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___474_2988.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___474_2988.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___474_2988.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___474_2988.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___474_2988.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___474_2988.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___474_2988.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___474_2988.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___474_2988.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___474_2988.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___474_2988.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___474_2988.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___474_2988.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___474_2988.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___474_2988.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___474_2988.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___474_2988.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___474_2988.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___474_2988.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___474_2988.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___474_2988.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___474_2988.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___474_2988.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___474_2988.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___474_2988.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___474_2988.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___474_2988.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___474_2988.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___474_2988.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___474_2988.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___474_2988.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___474_2988.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___478_3000  ->
                     match () with
                     | () ->
                         let uu____3009 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3009) ()
                with
                | FStar_Errors.Err (uu____3036,msg) ->
                    let uu____3040 = tts e1 t  in
                    let uu____3042 =
                      let uu____3044 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3044
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3040 uu____3042 msg
                | FStar_Errors.Error (uu____3054,msg,uu____3056) ->
                    let uu____3059 = tts e1 t  in
                    let uu____3061 =
                      let uu____3063 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3063
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3059 uu____3061 msg))
  
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
             (fun uu____3116  ->
                let uu____3117 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3117)
             (fun uu____3122  ->
                let e1 =
                  let uu___495_3124 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___495_3124.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___495_3124.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___495_3124.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___495_3124.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___495_3124.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___495_3124.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___495_3124.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___495_3124.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___495_3124.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___495_3124.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___495_3124.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___495_3124.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___495_3124.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___495_3124.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___495_3124.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___495_3124.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___495_3124.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___495_3124.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___495_3124.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___495_3124.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___495_3124.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___495_3124.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___495_3124.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___495_3124.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___495_3124.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___495_3124.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___495_3124.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___495_3124.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___495_3124.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___495_3124.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___495_3124.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___495_3124.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___495_3124.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___495_3124.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___495_3124.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___495_3124.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___495_3124.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___495_3124.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___495_3124.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___495_3124.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___495_3124.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___495_3124.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___499_3139  ->
                     match () with
                     | () ->
                         let uu____3148 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3148 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3186,msg) ->
                    let uu____3190 = tts e1 t  in
                    let uu____3192 =
                      let uu____3194 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3194
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3190 uu____3192 msg
                | FStar_Errors.Error (uu____3204,msg,uu____3206) ->
                    let uu____3209 = tts e1 t  in
                    let uu____3211 =
                      let uu____3213 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3213
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3209 uu____3211 msg))
  
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
             (fun uu____3266  ->
                let uu____3267 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3267)
             (fun uu____3273  ->
                let e1 =
                  let uu___520_3275 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___520_3275.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___520_3275.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___520_3275.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___520_3275.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___520_3275.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___520_3275.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___520_3275.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___520_3275.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___520_3275.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___520_3275.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___520_3275.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___520_3275.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___520_3275.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___520_3275.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___520_3275.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___520_3275.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___520_3275.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___520_3275.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___520_3275.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___520_3275.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___520_3275.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___520_3275.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___520_3275.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___520_3275.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___520_3275.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___520_3275.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___520_3275.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___520_3275.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___520_3275.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___520_3275.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___520_3275.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___520_3275.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___520_3275.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___520_3275.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___520_3275.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___520_3275.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___520_3275.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___520_3275.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___520_3275.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___520_3275.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___520_3275.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___520_3275.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___523_3278 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___523_3278.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___523_3278.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___523_3278.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___523_3278.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___523_3278.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___523_3278.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___523_3278.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___523_3278.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___523_3278.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___523_3278.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___523_3278.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___523_3278.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___523_3278.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___523_3278.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___523_3278.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___523_3278.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___523_3278.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___523_3278.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___523_3278.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___523_3278.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___523_3278.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___523_3278.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___523_3278.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___523_3278.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___523_3278.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___523_3278.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___523_3278.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___523_3278.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___523_3278.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___523_3278.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___523_3278.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___523_3278.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___523_3278.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___523_3278.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___523_3278.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___523_3278.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___523_3278.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___523_3278.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___523_3278.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___523_3278.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___523_3278.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___523_3278.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___527_3290  ->
                     match () with
                     | () ->
                         let uu____3299 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3299) ()
                with
                | FStar_Errors.Err (uu____3326,msg) ->
                    let uu____3330 = tts e2 t  in
                    let uu____3332 =
                      let uu____3334 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3334
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3330 uu____3332 msg
                | FStar_Errors.Error (uu____3344,msg,uu____3346) ->
                    let uu____3349 = tts e2 t  in
                    let uu____3351 =
                      let uu____3353 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3353
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3349 uu____3351 msg))
  
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
  fun uu____3388  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___548_3407 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___548_3407.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___548_3407.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___548_3407.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___548_3407.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___548_3407.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___548_3407.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___548_3407.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___548_3407.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___548_3407.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___548_3407.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___548_3407.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___548_3407.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3432 = get_guard_policy ()  in
      bind uu____3432
        (fun old_pol  ->
           let uu____3438 = set_guard_policy pol  in
           bind uu____3438
             (fun uu____3442  ->
                bind t
                  (fun r  ->
                     let uu____3446 = set_guard_policy old_pol  in
                     bind uu____3446 (fun uu____3450  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3454 = let uu____3459 = cur_goal ()  in trytac uu____3459  in
  bind uu____3454
    (fun uu___0_3466  ->
       match uu___0_3466 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3472 = FStar_Options.peek ()  in ret uu____3472)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3497  ->
             let uu____3498 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3498)
          (fun uu____3503  ->
             let uu____3504 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3504
               (fun uu____3508  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3512 =
                         let uu____3513 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3513.FStar_TypeChecker_Env.guard_f  in
                       match uu____3512 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3517 = istrivial e f  in
                           if uu____3517
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3530 =
                                          let uu____3536 =
                                            let uu____3538 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3538
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3536)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3530);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3544  ->
                                           let uu____3545 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3545)
                                        (fun uu____3550  ->
                                           let uu____3551 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3551
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___577_3559 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___577_3559.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___577_3559.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___577_3559.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___577_3559.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3563  ->
                                           let uu____3564 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3564)
                                        (fun uu____3569  ->
                                           let uu____3570 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3570
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___584_3578 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___584_3578.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___584_3578.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___584_3578.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___584_3578.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3582  ->
                                           let uu____3583 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3583)
                                        (fun uu____3587  ->
                                           try
                                             (fun uu___591_3592  ->
                                                match () with
                                                | () ->
                                                    let uu____3595 =
                                                      let uu____3597 =
                                                        let uu____3599 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3599
                                                         in
                                                      Prims.op_Negation
                                                        uu____3597
                                                       in
                                                    if uu____3595
                                                    then
                                                      mlog
                                                        (fun uu____3606  ->
                                                           let uu____3607 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3607)
                                                        (fun uu____3611  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___590_3616 ->
                                               mlog
                                                 (fun uu____3621  ->
                                                    let uu____3622 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3622)
                                                 (fun uu____3626  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____3638 =
      let uu____3641 = cur_goal ()  in
      bind uu____3641
        (fun goal  ->
           let uu____3647 =
             let uu____3656 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3656 t  in
           bind uu____3647
             (fun uu____3668  ->
                match uu____3668 with
                | (uu____3677,lc,uu____3679) ->
                    let uu____3680 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____3680))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____3638
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3696 =
      let uu____3701 = tcc t  in
      bind uu____3701 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3696
  
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
            let uu____3753 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3753 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3765  ->
    let uu____3768 = cur_goal ()  in
    bind uu____3768
      (fun goal  ->
         let uu____3774 =
           let uu____3776 = FStar_Tactics_Types.goal_env goal  in
           let uu____3777 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3776 uu____3777  in
         if uu____3774
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3783 =
              let uu____3785 = FStar_Tactics_Types.goal_env goal  in
              let uu____3786 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3785 uu____3786  in
            fail1 "Not a trivial goal: %s" uu____3783))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3837 =
               try
                 (fun uu___649_3860  ->
                    match () with
                    | () ->
                        let uu____3871 =
                          let uu____3880 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3880
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3871) ()
               with | uu___648_3891 -> fail "divide: not enough goals"  in
             bind uu____3837
               (fun uu____3928  ->
                  match uu____3928 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___631_3954 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___631_3954.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___631_3954.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___631_3954.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___631_3954.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___631_3954.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___631_3954.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___631_3954.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___631_3954.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___631_3954.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___631_3954.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___631_3954.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3955 = set lp  in
                      bind uu____3955
                        (fun uu____3963  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___637_3979 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___637_3979.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___637_3979.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___637_3979.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___637_3979.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___637_3979.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___637_3979.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___637_3979.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___637_3979.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___637_3979.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___637_3979.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___637_3979.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3980 = set rp  in
                                     bind uu____3980
                                       (fun uu____3988  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___643_4004 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___643_4004.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___643_4004.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4005 = set p'
                                                       in
                                                    bind uu____4005
                                                      (fun uu____4013  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4019 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4041 = divide FStar_BigInt.one f idtac  in
    bind uu____4041
      (fun uu____4054  -> match uu____4054 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4092::uu____4093 ->
             let uu____4096 =
               let uu____4105 = map tau  in
               divide FStar_BigInt.one tau uu____4105  in
             bind uu____4096
               (fun uu____4123  ->
                  match uu____4123 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4165 =
        bind t1
          (fun uu____4170  ->
             let uu____4171 = map t2  in
             bind uu____4171 (fun uu____4179  -> ret ()))
         in
      focus uu____4165
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4189  ->
    let uu____4192 =
      let uu____4195 = cur_goal ()  in
      bind uu____4195
        (fun goal  ->
           let uu____4204 =
             let uu____4211 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4211  in
           match uu____4204 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4220 =
                 let uu____4222 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4222  in
               if uu____4220
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4231 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4231 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4247 = new_uvar "intro" env' typ'  in
                  bind uu____4247
                    (fun uu____4264  ->
                       match uu____4264 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4288 = set_solution goal sol  in
                           bind uu____4288
                             (fun uu____4294  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4296 =
                                  let uu____4299 = bnorm_goal g  in
                                  replace_cur uu____4299  in
                                bind uu____4296 (fun uu____4301  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4306 =
                 let uu____4308 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4309 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4308 uu____4309  in
               fail1 "goal is not an arrow (%s)" uu____4306)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4192
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4327  ->
    let uu____4334 = cur_goal ()  in
    bind uu____4334
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4353 =
            let uu____4360 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4360  in
          match uu____4353 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4373 =
                let uu____4375 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4375  in
              if uu____4373
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4392 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4392
                    in
                 let bs =
                   let uu____4403 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4403; b]  in
                 let env' =
                   let uu____4429 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4429 bs  in
                 let uu____4430 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4430
                   (fun uu____4456  ->
                      match uu____4456 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4470 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4473 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4470
                              FStar_Parser_Const.effect_Tot_lid uu____4473 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4491 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4491 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4513 =
                                   let uu____4514 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4514.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4513
                                  in
                               let uu____4530 = set_solution goal tm  in
                               bind uu____4530
                                 (fun uu____4539  ->
                                    let uu____4540 =
                                      let uu____4543 =
                                        bnorm_goal
                                          (let uu___714_4546 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___714_4546.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___714_4546.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___714_4546.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___714_4546.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4543  in
                                    bind uu____4540
                                      (fun uu____4553  ->
                                         let uu____4554 =
                                           let uu____4559 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4559, b)  in
                                         ret uu____4554)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4568 =
                let uu____4570 = FStar_Tactics_Types.goal_env goal  in
                let uu____4571 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4570 uu____4571  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4568))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4591 = cur_goal ()  in
    bind uu____4591
      (fun goal  ->
         mlog
           (fun uu____4598  ->
              let uu____4599 =
                let uu____4601 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4601  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4599)
           (fun uu____4607  ->
              let steps =
                let uu____4611 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4611
                 in
              let t =
                let uu____4615 = FStar_Tactics_Types.goal_env goal  in
                let uu____4616 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4615 uu____4616  in
              let uu____4617 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4617))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4642 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4650 -> g.FStar_Tactics_Types.opts
                 | uu____4653 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4658  ->
                    let uu____4659 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4659)
                 (fun uu____4664  ->
                    let uu____4665 = __tc_lax e t  in
                    bind uu____4665
                      (fun uu____4686  ->
                         match uu____4686 with
                         | (t1,uu____4696,uu____4697) ->
                             let steps =
                               let uu____4701 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4701
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4707  ->
                                  let uu____4708 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4708)
                               (fun uu____4712  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4642
  
let (refine_intro : unit -> unit tac) =
  fun uu____4725  ->
    let uu____4728 =
      let uu____4731 = cur_goal ()  in
      bind uu____4731
        (fun g  ->
           let uu____4738 =
             let uu____4749 = FStar_Tactics_Types.goal_env g  in
             let uu____4750 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4749 uu____4750
              in
           match uu____4738 with
           | (uu____4753,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4779 =
                 let uu____4784 =
                   let uu____4789 =
                     let uu____4790 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4790]  in
                   FStar_Syntax_Subst.open_term uu____4789 phi  in
                 match uu____4784 with
                 | (bvs,phi1) ->
                     let uu____4815 =
                       let uu____4816 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4816  in
                     (uu____4815, phi1)
                  in
               (match uu____4779 with
                | (bv1,phi1) ->
                    let uu____4835 =
                      let uu____4838 = FStar_Tactics_Types.goal_env g  in
                      let uu____4839 =
                        let uu____4840 =
                          let uu____4843 =
                            let uu____4844 =
                              let uu____4851 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4851)  in
                            FStar_Syntax_Syntax.NT uu____4844  in
                          [uu____4843]  in
                        FStar_Syntax_Subst.subst uu____4840 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4838
                        uu____4839 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4835
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4860  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4728
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4883 = cur_goal ()  in
      bind uu____4883
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4892 = FStar_Tactics_Types.goal_env goal  in
               let uu____4893 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4892 uu____4893
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4896 = __tc env t  in
           bind uu____4896
             (fun uu____4915  ->
                match uu____4915 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4930  ->
                         let uu____4931 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4933 =
                           let uu____4935 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4935
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4931 uu____4933)
                      (fun uu____4939  ->
                         let uu____4940 =
                           let uu____4943 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4943 guard  in
                         bind uu____4940
                           (fun uu____4946  ->
                              mlog
                                (fun uu____4950  ->
                                   let uu____4951 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4953 =
                                     let uu____4955 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4955
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4951 uu____4953)
                                (fun uu____4959  ->
                                   let uu____4960 =
                                     let uu____4964 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4965 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4964 typ uu____4965  in
                                   bind uu____4960
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4975 =
                                             let uu____4977 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4977 t1  in
                                           let uu____4978 =
                                             let uu____4980 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4980 typ  in
                                           let uu____4981 =
                                             let uu____4983 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4984 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4983 uu____4984  in
                                           let uu____4985 =
                                             let uu____4987 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4988 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4987 uu____4988  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4975 uu____4978 uu____4981
                                             uu____4985)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5014 =
          mlog
            (fun uu____5019  ->
               let uu____5020 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5020)
            (fun uu____5025  ->
               let uu____5026 =
                 let uu____5033 = __exact_now set_expected_typ1 tm  in
                 catch uu____5033  in
               bind uu____5026
                 (fun uu___2_5042  ->
                    match uu___2_5042 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5053  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5057  ->
                             let uu____5058 =
                               let uu____5065 =
                                 let uu____5068 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5068
                                   (fun uu____5073  ->
                                      let uu____5074 = refine_intro ()  in
                                      bind uu____5074
                                        (fun uu____5078  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5065  in
                             bind uu____5058
                               (fun uu___1_5085  ->
                                  match uu___1_5085 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5094  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5097  -> ret ())
                                  | FStar_Util.Inl uu____5098 ->
                                      mlog
                                        (fun uu____5100  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5103  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5014
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5155 = f x  in
          bind uu____5155
            (fun y  ->
               let uu____5163 = mapM f xs  in
               bind uu____5163 (fun ys  -> ret (y :: ys)))
  
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
          let uu____5235 = do_unify e ty1 ty2  in
          bind uu____5235
            (fun uu___3_5249  ->
               if uu___3_5249
               then ret acc
               else
                 (let uu____5269 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____5269 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____5290 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____5292 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____5290
                        uu____5292
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____5309 =
                        let uu____5311 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____5311  in
                      if uu____5309
                      then fail "Codomain is effectful"
                      else
                        (let uu____5335 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____5335
                           (fun uu____5362  ->
                              match uu____5362 with
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
      let uu____5454 =
        mlog
          (fun uu____5459  ->
             let uu____5460 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5460)
          (fun uu____5465  ->
             let uu____5466 = cur_goal ()  in
             bind uu____5466
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5474 = __tc e tm  in
                  bind uu____5474
                    (fun uu____5495  ->
                       match uu____5495 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5508 =
                             let uu____5519 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5519  in
                           bind uu____5508
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____5557)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____5561 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5584  ->
                                       fun w  ->
                                         match uu____5584 with
                                         | (uvt,q,uu____5602) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5634 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5651  ->
                                       fun s  ->
                                         match uu____5651 with
                                         | (uu____5663,uu____5664,uv) ->
                                             let uu____5666 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5666) uvs uu____5634
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5676 = solve' goal w  in
                                bind uu____5676
                                  (fun uu____5681  ->
                                     let uu____5682 =
                                       mapM
                                         (fun uu____5699  ->
                                            match uu____5699 with
                                            | (uvt,q,uv) ->
                                                let uu____5711 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5711 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5716 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5717 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5717
                                                     then ret ()
                                                     else
                                                       (let uu____5724 =
                                                          let uu____5727 =
                                                            bnorm_goal
                                                              (let uu___875_5730
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___875_5730.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___875_5730.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___875_5730.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5727]  in
                                                        add_goals uu____5724)))
                                         uvs
                                        in
                                     bind uu____5682
                                       (fun uu____5735  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5454
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5763 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5763
    then
      let uu____5772 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5787 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5840 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5772 with
      | (pre,post) ->
          let post1 =
            let uu____5873 =
              let uu____5884 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5884]  in
            FStar_Syntax_Util.mk_app post uu____5873  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5915 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5915
       then
         let uu____5924 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5924
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
            let uu____6003 = f x e  in
            bind uu____6003 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6018 =
      let uu____6021 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6028  ->
                  let uu____6029 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6029)
               (fun uu____6035  ->
                  let is_unit_t t =
                    let uu____6043 =
                      let uu____6044 = FStar_Syntax_Subst.compress t  in
                      uu____6044.FStar_Syntax_Syntax.n  in
                    match uu____6043 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6050 -> false  in
                  let uu____6052 = cur_goal ()  in
                  bind uu____6052
                    (fun goal  ->
                       mlog
                         (fun uu____6059  ->
                            let uu____6060 = goal_to_string_verbose goal  in
                            FStar_Util.print1 "apply_lemma: goal = %s\n"
                              uu____6060)
                         (fun uu____6065  ->
                            let uu____6066 =
                              let uu____6075 =
                                FStar_Tactics_Types.goal_env goal  in
                              __tc uu____6075 tm  in
                            bind uu____6066
                              (fun uu____6086  ->
                                 match uu____6086 with
                                 | (tm1,t,guard) ->
                                     mlog
                                       (fun uu____6101  ->
                                          let uu____6102 =
                                            FStar_Syntax_Print.term_to_string
                                              tm1
                                             in
                                          let uu____6104 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          FStar_Util.print2
                                            "apply_lemma: tc_goal = %s, %s\n"
                                            uu____6102 uu____6104)
                                       (fun uu____6112  ->
                                          let uu____6113 =
                                            FStar_Syntax_Util.arrow_formals_comp
                                              t
                                             in
                                          match uu____6113 with
                                          | (bs,comp) ->
                                              let uu____6146 =
                                                lemma_or_sq comp  in
                                              (match uu____6146 with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   fail
                                                     "not a lemma or squashed function"
                                               | FStar_Pervasives_Native.Some
                                                   (pre,post) ->
                                                   let uu____6166 =
                                                     fold_left
                                                       (fun uu____6228  ->
                                                          fun uu____6229  ->
                                                            match (uu____6228,
                                                                    uu____6229)
                                                            with
                                                            | ((b,aq),
                                                               (uvs,imps,subst1))
                                                                ->
                                                                let b_t =
                                                                  FStar_Syntax_Subst.subst
                                                                    subst1
                                                                    b.FStar_Syntax_Syntax.sort
                                                                   in
                                                                let uu____6380
                                                                  =
                                                                  is_unit_t
                                                                    b_t
                                                                   in
                                                                if uu____6380
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
                                                                  (let uu____6503
                                                                    =
                                                                    let uu____6510
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    new_uvar
                                                                    "apply_lemma"
                                                                    uu____6510
                                                                    b_t  in
                                                                   bind
                                                                    uu____6503
                                                                    (fun
                                                                    uu____6541
                                                                     ->
                                                                    match uu____6541
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
                                                   bind uu____6166
                                                     (fun uu____6722  ->
                                                        match uu____6722 with
                                                        | (uvs,implicits,subst1)
                                                            ->
                                                            mlog
                                                              (fun uu____6784
                                                                  ->
                                                                 let uu____6785
                                                                   =
                                                                   FStar_Syntax_Print.subst_to_string
                                                                    subst1
                                                                    in
                                                                 FStar_Util.print1
                                                                   "apply_lemma: subst = %s"
                                                                   uu____6785)
                                                              (fun uu____6794
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
                                                                 let uu____6823
                                                                   =
                                                                   let uu____6827
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   let uu____6828
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    post1  in
                                                                   let uu____6829
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal  in
                                                                   do_unify
                                                                    uu____6827
                                                                    uu____6828
                                                                    uu____6829
                                                                    in
                                                                 bind
                                                                   uu____6823
                                                                   (fun b  ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    b
                                                                    then
                                                                    let uu____6840
                                                                    =
                                                                    let uu____6842
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    tts
                                                                    uu____6842
                                                                    tm1  in
                                                                    let uu____6843
                                                                    =
                                                                    let uu____6845
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6846
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    post1  in
                                                                    tts
                                                                    uu____6845
                                                                    uu____6846
                                                                     in
                                                                    let uu____6847
                                                                    =
                                                                    let uu____6849
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6850
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal  in
                                                                    tts
                                                                    uu____6849
                                                                    uu____6850
                                                                     in
                                                                    fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu____6840
                                                                    uu____6843
                                                                    uu____6847
                                                                    else
                                                                    (let uu____6854
                                                                    =
                                                                    solve'
                                                                    goal
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    bind
                                                                    uu____6854
                                                                    (fun
                                                                    uu____6862
                                                                     ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu____6888
                                                                    =
                                                                    let uu____6891
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6891
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6888
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
                                                                    let uu____6927
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6927)
                                                                    goals  in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu____6944
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                    match uu____6944
                                                                    with
                                                                    | 
                                                                    (hd1,uu____6963)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6990)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7007
                                                                    -> false)
                                                                     in
                                                                    let uu____7009
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    implicits1
                                                                    (mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let t1 =
                                                                    FStar_Util.now
                                                                    ()  in
                                                                    let uu____7052
                                                                    = imp  in
                                                                    match uu____7052
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7063
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7063
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7085)
                                                                    ->
                                                                    let uu____7110
                                                                    =
                                                                    let uu____7111
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7111.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7110
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7119)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___990_7139
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___990_7139.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___990_7139.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___990_7139.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___990_7139.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7142
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7148
                                                                     ->
                                                                    let uu____7149
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7151
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7149
                                                                    uu____7151)
                                                                    (fun
                                                                    uu____7158
                                                                     ->
                                                                    let env =
                                                                    let uu___995_7160
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___995_7160.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7163
                                                                    =
                                                                    let uu____7166
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7170
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7172
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7170
                                                                    uu____7172
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7178
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7166
                                                                    uu____7178
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7163
                                                                    (fun
                                                                    uu____7182
                                                                     ->
                                                                    ret []))))))
                                                                     in
                                                                    bind
                                                                    uu____7009
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
                                                                    let uu____7246
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7246
                                                                    then
                                                                    let uu____7251
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7251
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
                                                                    let uu____7266
                                                                    =
                                                                    let uu____7268
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7268
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7266)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7269
                                                                    =
                                                                    let uu____7272
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7272
                                                                    guard  in
                                                                    bind
                                                                    uu____7269
                                                                    (fun
                                                                    uu____7275
                                                                     ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7278
                                                                     ->
                                                                    let uu____7279
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    pre1  in
                                                                    FStar_Util.print1
                                                                    ">>>apply_lemma proc_guard done ... guard = %s\n"
                                                                    uu____7279)
                                                                    (fun
                                                                    uu____7284
                                                                     ->
                                                                    let uu____7285
                                                                    =
                                                                    let uu____7288
                                                                    =
                                                                    let uu____7290
                                                                    =
                                                                    let uu____7292
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7293
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7292
                                                                    uu____7293
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7290
                                                                     in
                                                                    if
                                                                    uu____7288
                                                                    then
                                                                    let uu____7297
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7297
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7285
                                                                    (fun
                                                                    uu____7302
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))))
         in
      focus uu____6021  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6018
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7326 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7326 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7336::(e1,uu____7338)::(e2,uu____7340)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____7401 ->
        let uu____7404 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7404 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____7419 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____7419);
              (let uu____7422 = FStar_Syntax_Util.head_and_args t  in
               match uu____7422 with
               | (hd1,args) ->
                   let uu____7471 =
                     let uu____7486 =
                       let uu____7487 = FStar_Syntax_Subst.compress hd1  in
                       uu____7487.FStar_Syntax_Syntax.n  in
                     (uu____7486, args)  in
                   (match uu____7471 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____7507,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____7508))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____7573 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____7575 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____7573
                            uu____7575);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____7582 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7619 = destruct_eq' typ  in
    match uu____7619 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7649 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7649 with
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
        let uu____7718 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7718 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7776 = aux e'  in
               FStar_Util.map_opt uu____7776
                 (fun uu____7807  ->
                    match uu____7807 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7833 = aux e  in
      FStar_Util.map_opt uu____7833
        (fun uu____7864  ->
           match uu____7864 with
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
          let uu____7938 =
            let uu____7949 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____7949  in
          FStar_Util.map_opt uu____7938
            (fun uu____7967  ->
               match uu____7967 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1095_7989 = bv  in
                     let uu____7990 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1095_7989.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1095_7989.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7990
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1099_7998 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7999 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____8008 =
                       let uu____8011 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____8011  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1099_7998.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7999;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____8008;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1099_7998.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1099_7998.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1099_7998.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1099_7998.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1102_8012 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1102_8012.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1102_8012.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1102_8012.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1102_8012.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8023 =
      let uu____8026 = cur_goal ()  in
      bind uu____8026
        (fun goal  ->
           let uu____8034 = h  in
           match uu____8034 with
           | (bv,uu____8038) ->
               mlog
                 (fun uu____8046  ->
                    let uu____8047 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8049 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8047
                      uu____8049)
                 (fun uu____8054  ->
                    let uu____8055 =
                      let uu____8066 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8066  in
                    match uu____8055 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8093 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8093 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8108 =
                               let uu____8109 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8109.FStar_Syntax_Syntax.n  in
                             (match uu____8108 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1125_8126 = bv2  in
                                    let uu____8127 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1125_8126.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1125_8126.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8127
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1129_8135 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8136 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8145 =
                                      let uu____8148 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8148
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1129_8135.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8136;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8145;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1129_8135.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1129_8135.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1129_8135.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1129_8135.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1132_8151 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1132_8151.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1132_8151.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1132_8151.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1132_8151.FStar_Tactics_Types.label)
                                     })
                              | uu____8152 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8154 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8023
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____8184 =
        let uu____8187 = cur_goal ()  in
        bind uu____8187
          (fun goal  ->
             let uu____8198 = b  in
             match uu____8198 with
             | (bv,uu____8202) ->
                 let bv' =
                   let uu____8208 =
                     let uu___1143_8209 = bv  in
                     let uu____8210 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8210;
                       FStar_Syntax_Syntax.index =
                         (uu___1143_8209.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1143_8209.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8208  in
                 let s1 =
                   let uu____8215 =
                     let uu____8216 =
                       let uu____8223 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8223)  in
                     FStar_Syntax_Syntax.NT uu____8216  in
                   [uu____8215]  in
                 let uu____8228 = subst_goal bv bv' s1 goal  in
                 (match uu____8228 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8184
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8250 =
      let uu____8253 = cur_goal ()  in
      bind uu____8253
        (fun goal  ->
           let uu____8262 = b  in
           match uu____8262 with
           | (bv,uu____8266) ->
               let uu____8271 =
                 let uu____8282 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8282  in
               (match uu____8271 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8309 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8309 with
                     | (ty,u) ->
                         let uu____8318 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8318
                           (fun uu____8337  ->
                              match uu____8337 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1167_8347 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1167_8347.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1167_8347.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8351 =
                                      let uu____8352 =
                                        let uu____8359 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8359)  in
                                      FStar_Syntax_Syntax.NT uu____8352  in
                                    [uu____8351]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1172_8371 = b1  in
                                         let uu____8372 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1172_8371.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1172_8371.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8372
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8379  ->
                                       let new_goal =
                                         let uu____8381 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8382 =
                                           let uu____8383 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8383
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8381 uu____8382
                                          in
                                       let uu____8384 = add_goals [new_goal]
                                          in
                                       bind uu____8384
                                         (fun uu____8389  ->
                                            let uu____8390 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8390
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8250
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8416 =
        let uu____8419 = cur_goal ()  in
        bind uu____8419
          (fun goal  ->
             let uu____8428 = b  in
             match uu____8428 with
             | (bv,uu____8432) ->
                 let uu____8437 =
                   let uu____8448 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8448  in
                 (match uu____8437 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8478 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8478
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1193_8483 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1193_8483.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1193_8483.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8485 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8485))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8416
  
let (revert : unit -> unit tac) =
  fun uu____8498  ->
    let uu____8501 = cur_goal ()  in
    bind uu____8501
      (fun goal  ->
         let uu____8507 =
           let uu____8514 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8514  in
         match uu____8507 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8531 =
                 let uu____8534 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8534  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8531
                in
             let uu____8549 = new_uvar "revert" env' typ'  in
             bind uu____8549
               (fun uu____8565  ->
                  match uu____8565 with
                  | (r,u_r) ->
                      let uu____8574 =
                        let uu____8577 =
                          let uu____8578 =
                            let uu____8579 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8579.FStar_Syntax_Syntax.pos  in
                          let uu____8582 =
                            let uu____8587 =
                              let uu____8588 =
                                let uu____8597 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8597  in
                              [uu____8588]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8587  in
                          uu____8582 FStar_Pervasives_Native.None uu____8578
                           in
                        set_solution goal uu____8577  in
                      bind uu____8574
                        (fun uu____8616  ->
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
      let uu____8630 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8630
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8646 = cur_goal ()  in
    bind uu____8646
      (fun goal  ->
         mlog
           (fun uu____8654  ->
              let uu____8655 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8657 =
                let uu____8659 =
                  let uu____8661 =
                    let uu____8670 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8670  in
                  FStar_All.pipe_right uu____8661 FStar_List.length  in
                FStar_All.pipe_right uu____8659 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8655 uu____8657)
           (fun uu____8691  ->
              let uu____8692 =
                let uu____8703 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8703  in
              match uu____8692 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8748 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8748
                        then
                          let uu____8753 =
                            let uu____8755 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8755
                             in
                          fail uu____8753
                        else check1 bvs2
                     in
                  let uu____8760 =
                    let uu____8762 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8762  in
                  if uu____8760
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8769 = check1 bvs  in
                     bind uu____8769
                       (fun uu____8775  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8777 =
                            let uu____8784 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8784  in
                          bind uu____8777
                            (fun uu____8794  ->
                               match uu____8794 with
                               | (ut,uvar_ut) ->
                                   let uu____8803 = set_solution goal ut  in
                                   bind uu____8803
                                     (fun uu____8808  ->
                                        let uu____8809 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8809))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8817  ->
    let uu____8820 = cur_goal ()  in
    bind uu____8820
      (fun goal  ->
         let uu____8826 =
           let uu____8833 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8833  in
         match uu____8826 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8842) ->
             let uu____8847 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8847)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8860 = cur_goal ()  in
    bind uu____8860
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8870 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8870  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8873  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____8886 = cur_goal ()  in
    bind uu____8886
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8896 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8896  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8899  -> add_goals [g']))
  
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
            let uu____8940 = FStar_Syntax_Subst.compress t  in
            uu____8940.FStar_Syntax_Syntax.n  in
          let uu____8943 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1377_8950 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1377_8950.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1377_8950.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____8943
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____8967 =
                   let uu____8968 = FStar_Syntax_Subst.compress t1  in
                   uu____8968.FStar_Syntax_Syntax.n  in
                 match uu____8967 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8999 = ff hd1  in
                     bind uu____8999
                       (fun hd2  ->
                          let fa uu____9025 =
                            match uu____9025 with
                            | (a,q) ->
                                let uu____9046 = ff a  in
                                bind uu____9046 (fun a1  -> ret (a1, q))
                             in
                          let uu____9065 = mapM fa args  in
                          bind uu____9065
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9147 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9147 with
                      | (bs1,t') ->
                          let uu____9156 =
                            let uu____9159 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9159 t'  in
                          bind uu____9156
                            (fun t''  ->
                               let uu____9163 =
                                 let uu____9164 =
                                   let uu____9183 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9192 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9183, uu____9192, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9164  in
                               ret uu____9163))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9267 = ff hd1  in
                     bind uu____9267
                       (fun hd2  ->
                          let ffb br =
                            let uu____9282 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9282 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9314 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9314  in
                                let uu____9315 = ff1 e  in
                                bind uu____9315
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9330 = mapM ffb brs  in
                          bind uu____9330
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9374;
                          FStar_Syntax_Syntax.lbtyp = uu____9375;
                          FStar_Syntax_Syntax.lbeff = uu____9376;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9378;
                          FStar_Syntax_Syntax.lbpos = uu____9379;_}::[]),e)
                     ->
                     let lb =
                       let uu____9407 =
                         let uu____9408 = FStar_Syntax_Subst.compress t1  in
                         uu____9408.FStar_Syntax_Syntax.n  in
                       match uu____9407 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9412) -> lb
                       | uu____9428 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9438 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9438
                         (fun def1  ->
                            ret
                              (let uu___1330_9444 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1330_9444.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1330_9444.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1330_9444.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1330_9444.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1330_9444.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1330_9444.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9445 = fflb lb  in
                     bind uu____9445
                       (fun lb1  ->
                          let uu____9455 =
                            let uu____9460 =
                              let uu____9461 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9461]  in
                            FStar_Syntax_Subst.open_term uu____9460 e  in
                          match uu____9455 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9491 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9491  in
                              let uu____9492 = ff1 e1  in
                              bind uu____9492
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9539 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9539
                         (fun def  ->
                            ret
                              (let uu___1348_9545 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1348_9545.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1348_9545.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1348_9545.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1348_9545.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1348_9545.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1348_9545.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9546 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9546 with
                      | (lbs1,e1) ->
                          let uu____9561 = mapM fflb lbs1  in
                          bind uu____9561
                            (fun lbs2  ->
                               let uu____9573 = ff e1  in
                               bind uu____9573
                                 (fun e2  ->
                                    let uu____9581 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9581 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9652 = ff t2  in
                     bind uu____9652
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9683 = ff t2  in
                     bind uu____9683
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9690 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1372_9697 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1372_9697.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1372_9697.FStar_Syntax_Syntax.vars)
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
              let uu____9744 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1385_9753 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1385_9753.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1385_9753.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1385_9753.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1385_9753.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1385_9753.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1385_9753.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1385_9753.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1385_9753.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1385_9753.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1385_9753.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1385_9753.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1385_9753.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1385_9753.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1385_9753.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1385_9753.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1385_9753.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1385_9753.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1385_9753.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1385_9753.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1385_9753.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1385_9753.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1385_9753.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1385_9753.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1385_9753.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1385_9753.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1385_9753.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1385_9753.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1385_9753.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1385_9753.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1385_9753.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1385_9753.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1385_9753.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1385_9753.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1385_9753.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1385_9753.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1385_9753.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1385_9753.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1385_9753.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1385_9753.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1385_9753.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1385_9753.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1385_9753.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9744 with
              | (t1,lcomp,g) ->
                  let uu____9760 =
                    (let uu____9764 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9764) ||
                      (let uu____9767 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9767)
                     in
                  if uu____9760
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9778 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9778
                         (fun uu____9795  ->
                            match uu____9795 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9808  ->
                                      let uu____9809 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9811 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9809 uu____9811);
                                 (let uu____9814 =
                                    let uu____9817 =
                                      let uu____9818 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9818 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9817
                                      opts label1
                                     in
                                  bind uu____9814
                                    (fun uu____9822  ->
                                       let uu____9823 =
                                         bind tau
                                           (fun uu____9829  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9835  ->
                                                   let uu____9836 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9838 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9836 uu____9838);
                                              ret ut1)
                                          in
                                       focus uu____9823))))
                        in
                     let uu____9841 = catch rewrite_eq  in
                     bind uu____9841
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
          let uu____10053 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10053
            (fun t1  ->
               let uu____10061 =
                 f env
                   (let uu___1462_10069 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1462_10069.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1462_10069.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10061
                 (fun uu____10085  ->
                    match uu____10085 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10108 =
                               let uu____10109 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10109.FStar_Syntax_Syntax.n  in
                             match uu____10108 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10146 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10146
                                   (fun uu____10168  ->
                                      match uu____10168 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10184 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10184
                                            (fun uu____10208  ->
                                               match uu____10208 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1442_10238 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1442_10238.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1442_10238.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10280 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10280 with
                                  | (bs1,t') ->
                                      let uu____10295 =
                                        let uu____10302 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10302 ctrl1 t'
                                         in
                                      bind uu____10295
                                        (fun uu____10317  ->
                                           match uu____10317 with
                                           | (t'',ctrl2) ->
                                               let uu____10332 =
                                                 let uu____10339 =
                                                   let uu___1455_10342 = t4
                                                      in
                                                   let uu____10345 =
                                                     let uu____10346 =
                                                       let uu____10365 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10374 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10365,
                                                         uu____10374, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10346
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10345;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1455_10342.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1455_10342.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10339, ctrl2)  in
                                               ret uu____10332))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10427 -> ret (t3, ctrl1))))

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
              let uu____10473 = ctrl_tac_fold f env ctrl t  in
              bind uu____10473
                (fun uu____10494  ->
                   match uu____10494 with
                   | (t1,ctrl1) ->
                       let uu____10509 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10509
                         (fun uu____10533  ->
                            match uu____10533 with
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
                let uu____10624 =
                  let uu____10632 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10632
                    (fun uu____10643  ->
                       let uu____10644 = ctrl t1  in
                       bind uu____10644
                         (fun res  ->
                            let uu____10670 = trivial ()  in
                            bind uu____10670 (fun uu____10679  -> ret res)))
                   in
                bind uu____10624
                  (fun uu____10697  ->
                     match uu____10697 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10726 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1492_10735 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1492_10735.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1492_10735.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1492_10735.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1492_10735.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1492_10735.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1492_10735.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1492_10735.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1492_10735.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1492_10735.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1492_10735.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1492_10735.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1492_10735.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1492_10735.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1492_10735.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1492_10735.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1492_10735.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1492_10735.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1492_10735.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1492_10735.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1492_10735.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1492_10735.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1492_10735.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1492_10735.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1492_10735.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1492_10735.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1492_10735.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1492_10735.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1492_10735.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1492_10735.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1492_10735.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1492_10735.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1492_10735.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1492_10735.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1492_10735.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1492_10735.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1492_10735.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1492_10735.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1492_10735.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1492_10735.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1492_10735.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1492_10735.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1492_10735.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10726 with
                            | (t2,lcomp,g) ->
                                let uu____10746 =
                                  (let uu____10750 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10750) ||
                                    (let uu____10753 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10753)
                                   in
                                if uu____10746
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10769 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10769
                                     (fun uu____10790  ->
                                        match uu____10790 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10807  ->
                                                  let uu____10808 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10810 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10808 uu____10810);
                                             (let uu____10813 =
                                                let uu____10816 =
                                                  let uu____10817 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10817 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10816 opts label1
                                                 in
                                              bind uu____10813
                                                (fun uu____10825  ->
                                                   let uu____10826 =
                                                     bind rewriter
                                                       (fun uu____10840  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10846 
                                                               ->
                                                               let uu____10847
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10849
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10847
                                                                 uu____10849);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10826)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____10894 =
        bind get
          (fun ps  ->
             let uu____10904 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10904 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10942  ->
                       let uu____10943 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10943);
                  bind dismiss_all
                    (fun uu____10948  ->
                       let uu____10949 =
                         let uu____10956 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10956
                           keepGoing gt1
                          in
                       bind uu____10949
                         (fun uu____10966  ->
                            match uu____10966 with
                            | (gt',uu____10974) ->
                                (log ps
                                   (fun uu____10978  ->
                                      let uu____10979 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10979);
                                 (let uu____10982 = push_goals gs  in
                                  bind uu____10982
                                    (fun uu____10987  ->
                                       let uu____10988 =
                                         let uu____10991 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10991]  in
                                       add_goals uu____10988)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10894
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11016 =
        bind get
          (fun ps  ->
             let uu____11026 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11026 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11064  ->
                       let uu____11065 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11065);
                  bind dismiss_all
                    (fun uu____11070  ->
                       let uu____11071 =
                         let uu____11074 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11074 gt1
                          in
                       bind uu____11071
                         (fun gt'  ->
                            log ps
                              (fun uu____11082  ->
                                 let uu____11083 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11083);
                            (let uu____11086 = push_goals gs  in
                             bind uu____11086
                               (fun uu____11091  ->
                                  let uu____11092 =
                                    let uu____11095 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____11095]  in
                                  add_goals uu____11092))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____11016
  
let (trefl : unit -> unit tac) =
  fun uu____11108  ->
    let uu____11111 =
      let uu____11114 = cur_goal ()  in
      bind uu____11114
        (fun g  ->
           let uu____11132 =
             let uu____11137 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____11137  in
           match uu____11132 with
           | FStar_Pervasives_Native.Some t ->
               let uu____11145 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____11145 with
                | (hd1,args) ->
                    let uu____11184 =
                      let uu____11197 =
                        let uu____11198 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____11198.FStar_Syntax_Syntax.n  in
                      (uu____11197, args)  in
                    (match uu____11184 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____11212::(l,uu____11214)::(r,uu____11216)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____11263 =
                           let uu____11267 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____11267 l r  in
                         bind uu____11263
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____11278 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11278 l
                                    in
                                 let r1 =
                                   let uu____11280 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11280 r
                                    in
                                 let uu____11281 =
                                   let uu____11285 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____11285 l1 r1  in
                                 bind uu____11281
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____11295 =
                                           let uu____11297 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11297 l1  in
                                         let uu____11298 =
                                           let uu____11300 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____11300 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____11295 uu____11298))))
                     | (hd2,uu____11303) ->
                         let uu____11320 =
                           let uu____11322 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____11322 t  in
                         fail1 "trefl: not an equality (%s)" uu____11320))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11111
  
let (dup : unit -> unit tac) =
  fun uu____11339  ->
    let uu____11342 = cur_goal ()  in
    bind uu____11342
      (fun g  ->
         let uu____11348 =
           let uu____11355 = FStar_Tactics_Types.goal_env g  in
           let uu____11356 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11355 uu____11356  in
         bind uu____11348
           (fun uu____11366  ->
              match uu____11366 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1584_11376 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1584_11376.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1584_11376.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1584_11376.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1584_11376.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11379  ->
                       let uu____11380 =
                         let uu____11383 = FStar_Tactics_Types.goal_env g  in
                         let uu____11384 =
                           let uu____11385 =
                             let uu____11386 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11387 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11386
                               uu____11387
                              in
                           let uu____11388 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11389 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11385 uu____11388 u
                             uu____11389
                            in
                         add_irrelevant_goal "dup equation" uu____11383
                           uu____11384 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11380
                         (fun uu____11393  ->
                            let uu____11394 = add_goals [g']  in
                            bind uu____11394 (fun uu____11398  -> ret ())))))
  
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
              let uu____11524 = f x y  in
              if uu____11524 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11547 -> (acc, l11, l21)  in
        let uu____11562 = aux [] l1 l2  in
        match uu____11562 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11668 = get_phi g1  in
      match uu____11668 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11675 = get_phi g2  in
          (match uu____11675 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11688 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11688 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11719 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11719 phi1  in
                    let t2 =
                      let uu____11729 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11729 phi2  in
                    let uu____11738 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11738
                      (fun uu____11743  ->
                         let uu____11744 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11744
                           (fun uu____11751  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1635_11756 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11757 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1635_11756.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1635_11756.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1635_11756.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1635_11756.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11757;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1635_11756.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1635_11756.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1635_11756.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1635_11756.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1635_11756.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1635_11756.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1635_11756.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1635_11756.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1635_11756.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1635_11756.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1635_11756.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1635_11756.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1635_11756.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1635_11756.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1635_11756.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1635_11756.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1635_11756.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1635_11756.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1635_11756.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1635_11756.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1635_11756.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1635_11756.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1635_11756.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1635_11756.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1635_11756.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1635_11756.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1635_11756.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1635_11756.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1635_11756.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1635_11756.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1635_11756.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1635_11756.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1635_11756.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1635_11756.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1635_11756.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1635_11756.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1635_11756.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11761 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11761
                                (fun goal  ->
                                   mlog
                                     (fun uu____11771  ->
                                        let uu____11772 =
                                          goal_to_string_verbose g1  in
                                        let uu____11774 =
                                          goal_to_string_verbose g2  in
                                        let uu____11776 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11772 uu____11774 uu____11776)
                                     (fun uu____11780  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11788  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11804 =
               set
                 (let uu___1650_11809 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1650_11809.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1650_11809.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1650_11809.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1650_11809.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1650_11809.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1650_11809.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1650_11809.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1650_11809.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1650_11809.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1650_11809.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1650_11809.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1650_11809.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11804
               (fun uu____11812  ->
                  let uu____11813 = join_goals g1 g2  in
                  bind uu____11813 (fun g12  -> add_goals [g12]))
         | uu____11818 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11834 =
      let uu____11837 = cur_goal ()  in
      bind uu____11837
        (fun g  ->
           FStar_Options.push ();
           (let uu____11850 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11850);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1661_11857 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1661_11857.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1661_11857.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1661_11857.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1661_11857.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11834
  
let (top_env : unit -> env tac) =
  fun uu____11874  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11889  ->
    let uu____11893 = cur_goal ()  in
    bind uu____11893
      (fun g  ->
         let uu____11900 =
           (FStar_Options.lax ()) ||
             (let uu____11903 = FStar_Tactics_Types.goal_env g  in
              uu____11903.FStar_TypeChecker_Env.lax)
            in
         ret uu____11900)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11920 =
        mlog
          (fun uu____11925  ->
             let uu____11926 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11926)
          (fun uu____11931  ->
             let uu____11932 = cur_goal ()  in
             bind uu____11932
               (fun goal  ->
                  let env =
                    let uu____11940 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11940 ty  in
                  let uu____11941 = __tc_ghost env tm  in
                  bind uu____11941
                    (fun uu____11960  ->
                       match uu____11960 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11974  ->
                                let uu____11975 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11975)
                             (fun uu____11979  ->
                                mlog
                                  (fun uu____11982  ->
                                     let uu____11983 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11983)
                                  (fun uu____11988  ->
                                     let uu____11989 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11989
                                       (fun uu____11994  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11920
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12019 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12025 =
              let uu____12032 =
                let uu____12033 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12033
                 in
              new_uvar "uvar_env.2" env uu____12032  in
            bind uu____12025
              (fun uu____12050  ->
                 match uu____12050 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12019
        (fun typ  ->
           let uu____12062 = new_uvar "uvar_env" env typ  in
           bind uu____12062
             (fun uu____12077  ->
                match uu____12077 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12096 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12115 -> g.FStar_Tactics_Types.opts
             | uu____12118 -> FStar_Options.peek ()  in
           let uu____12121 = FStar_Syntax_Util.head_and_args t  in
           match uu____12121 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12141);
                FStar_Syntax_Syntax.pos = uu____12142;
                FStar_Syntax_Syntax.vars = uu____12143;_},uu____12144)
               ->
               let env1 =
                 let uu___1715_12186 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1715_12186.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1715_12186.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1715_12186.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1715_12186.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1715_12186.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1715_12186.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1715_12186.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1715_12186.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1715_12186.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1715_12186.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1715_12186.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1715_12186.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1715_12186.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1715_12186.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1715_12186.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1715_12186.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1715_12186.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1715_12186.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1715_12186.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1715_12186.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1715_12186.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1715_12186.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1715_12186.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1715_12186.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1715_12186.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1715_12186.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1715_12186.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1715_12186.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1715_12186.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1715_12186.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1715_12186.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1715_12186.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1715_12186.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1715_12186.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1715_12186.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1715_12186.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1715_12186.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1715_12186.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1715_12186.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1715_12186.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1715_12186.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1715_12186.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12190 =
                 let uu____12193 = bnorm_goal g  in [uu____12193]  in
               add_goals uu____12190
           | uu____12194 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12096
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12256 = if b then t2 else ret false  in
             bind uu____12256 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12282 = trytac comp  in
      bind uu____12282
        (fun uu___4_12294  ->
           match uu___4_12294 with
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
        let uu____12336 =
          bind get
            (fun ps  ->
               let uu____12344 = __tc e t1  in
               bind uu____12344
                 (fun uu____12365  ->
                    match uu____12365 with
                    | (t11,ty1,g1) ->
                        let uu____12378 = __tc e t2  in
                        bind uu____12378
                          (fun uu____12399  ->
                             match uu____12399 with
                             | (t21,ty2,g2) ->
                                 let uu____12412 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12412
                                   (fun uu____12419  ->
                                      let uu____12420 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12420
                                        (fun uu____12428  ->
                                           let uu____12429 =
                                             do_unify e ty1 ty2  in
                                           let uu____12433 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12429 uu____12433)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12336
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12481  ->
             let uu____12482 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12482
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
        (fun uu____12516  ->
           let uu____12517 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12517)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12528 =
      mlog
        (fun uu____12533  ->
           let uu____12534 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12534)
        (fun uu____12539  ->
           let uu____12540 = cur_goal ()  in
           bind uu____12540
             (fun g  ->
                let uu____12546 =
                  let uu____12555 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12555 ty  in
                bind uu____12546
                  (fun uu____12567  ->
                     match uu____12567 with
                     | (ty1,uu____12577,guard) ->
                         let uu____12579 =
                           let uu____12582 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12582 guard  in
                         bind uu____12579
                           (fun uu____12586  ->
                              let uu____12587 =
                                let uu____12591 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12592 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12591 uu____12592 ty1  in
                              bind uu____12587
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12601 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12601
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12608 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12609 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12608
                                          uu____12609
                                         in
                                      let nty =
                                        let uu____12611 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12611 ty1  in
                                      let uu____12612 =
                                        let uu____12616 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12616 ng nty  in
                                      bind uu____12612
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12625 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12625
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12528
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12699 =
      let uu____12708 = cur_goal ()  in
      bind uu____12708
        (fun g  ->
           let uu____12720 =
             let uu____12729 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12729 s_tm  in
           bind uu____12720
             (fun uu____12747  ->
                match uu____12747 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12765 =
                      let uu____12768 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12768 guard  in
                    bind uu____12765
                      (fun uu____12781  ->
                         let uu____12782 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12782 with
                         | (h,args) ->
                             let uu____12827 =
                               let uu____12834 =
                                 let uu____12835 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12835.FStar_Syntax_Syntax.n  in
                               match uu____12834 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12850;
                                      FStar_Syntax_Syntax.vars = uu____12851;_},us)
                                   -> ret (fv, us)
                               | uu____12861 -> fail "type is not an fv"  in
                             bind uu____12827
                               (fun uu____12882  ->
                                  match uu____12882 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12898 =
                                        let uu____12901 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12901 t_lid
                                         in
                                      (match uu____12898 with
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
                                                  (fun uu____12952  ->
                                                     let uu____12953 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12953 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12968 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12996
                                                                  =
                                                                  let uu____12999
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12999
                                                                    c_lid
                                                                   in
                                                                match uu____12996
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
                                                                    uu____13073
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
                                                                    let uu____13078
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13078
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13101
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13101
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13144
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____13144
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____13217
                                                                    =
                                                                    let uu____13219
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____13219
                                                                     in
                                                                    failwhen
                                                                    uu____13217
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13238
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
                                                                    uu___5_13255
                                                                    =
                                                                    match uu___5_13255
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13259)
                                                                    -> true
                                                                    | 
                                                                    uu____13262
                                                                    -> false
                                                                     in
                                                                    let uu____13266
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13266
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
                                                                    uu____13400
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
                                                                    uu____13462
                                                                     ->
                                                                    match uu____13462
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13482),
                                                                    (t,uu____13484))
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
                                                                    uu____13554
                                                                     ->
                                                                    match uu____13554
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13581),
                                                                    (t,uu____13583))
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
                                                                    uu____13642
                                                                     ->
                                                                    match uu____13642
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
                                                                    let uu____13697
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1879_13714
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1879_13714.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13697
                                                                    with
                                                                    | 
                                                                    (uu____13728,uu____13729,uu____13730,pat_t,uu____13732,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13739
                                                                    =
                                                                    let uu____13740
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13740
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13739
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13745
                                                                    =
                                                                    let uu____13754
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13754]
                                                                     in
                                                                    let uu____13773
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13745
                                                                    uu____13773
                                                                     in
                                                                    let nty =
                                                                    let uu____13779
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13779
                                                                     in
                                                                    let uu____13782
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13782
                                                                    (fun
                                                                    uu____13812
                                                                     ->
                                                                    match uu____13812
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
                                                                    let uu____13839
                                                                    =
                                                                    let uu____13850
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13850]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13839
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13886
                                                                    =
                                                                    let uu____13897
                                                                    =
                                                                    let uu____13902
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13902)
                                                                     in
                                                                    (g', br,
                                                                    uu____13897)
                                                                     in
                                                                    ret
                                                                    uu____13886))))))
                                                                    | 
                                                                    uu____13923
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12968
                                                           (fun goal_brs  ->
                                                              let uu____13973
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13973
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
                                                                  let uu____14046
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____14046
                                                                    (
                                                                    fun
                                                                    uu____14057
                                                                     ->
                                                                    let uu____14058
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14058
                                                                    (fun
                                                                    uu____14068
                                                                     ->
                                                                    ret infos))))
                                            | uu____14075 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12699
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14124::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14154 = init xs  in x :: uu____14154
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14167 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14176) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14242 = last args  in
          (match uu____14242 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14272 =
                 let uu____14273 =
                   let uu____14278 =
                     let uu____14279 =
                       let uu____14284 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14284  in
                     uu____14279 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14278, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14273  in
               FStar_All.pipe_left ret uu____14272)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14295,uu____14296) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14349 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14349 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14391 =
                      let uu____14392 =
                        let uu____14397 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14397)  in
                      FStar_Reflection_Data.Tv_Abs uu____14392  in
                    FStar_All.pipe_left ret uu____14391))
      | FStar_Syntax_Syntax.Tm_type uu____14400 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14425 ->
          let uu____14440 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14440 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14471 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14471 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14524 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14537 =
            let uu____14538 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14538  in
          FStar_All.pipe_left ret uu____14537
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14559 =
            let uu____14560 =
              let uu____14565 =
                let uu____14566 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14566  in
              (uu____14565, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14560  in
          FStar_All.pipe_left ret uu____14559
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14606 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14611 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14611 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14664 ->
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
             | FStar_Util.Inr uu____14706 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14710 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14710 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14730 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14736 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14791 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14791
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14812 =
                  let uu____14819 =
                    FStar_List.map
                      (fun uu____14832  ->
                         match uu____14832 with
                         | (p1,uu____14841) -> inspect_pat p1) ps
                     in
                  (fv, uu____14819)  in
                FStar_Reflection_Data.Pat_Cons uu____14812
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
              (fun uu___6_14937  ->
                 match uu___6_14937 with
                 | (pat,uu____14959,t5) ->
                     let uu____14977 = inspect_pat pat  in (uu____14977, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14986 ->
          ((let uu____14988 =
              let uu____14994 =
                let uu____14996 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14998 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14996 uu____14998
                 in
              (FStar_Errors.Warning_CantInspect, uu____14994)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14988);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14167
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15016 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15016
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15020 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15020
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15024 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15024
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15031 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15031
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15056 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15056
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15073 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15073
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15092 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15092
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15096 =
          let uu____15097 =
            let uu____15104 =
              let uu____15105 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15105  in
            FStar_Syntax_Syntax.mk uu____15104  in
          uu____15097 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15096
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15110 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15110
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15121 =
          let uu____15122 =
            let uu____15129 =
              let uu____15130 =
                let uu____15144 =
                  let uu____15147 =
                    let uu____15148 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15148]  in
                  FStar_Syntax_Subst.close uu____15147 t2  in
                ((false, [lb]), uu____15144)  in
              FStar_Syntax_Syntax.Tm_let uu____15130  in
            FStar_Syntax_Syntax.mk uu____15129  in
          uu____15122 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15121
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____15190 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15190 with
         | (lbs,body) ->
             let uu____15205 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15205)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15242 =
                let uu____15243 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15243  in
              FStar_All.pipe_left wrap uu____15242
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15250 =
                let uu____15251 =
                  let uu____15265 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15283 = pack_pat p1  in
                         (uu____15283, false)) ps
                     in
                  (fv, uu____15265)  in
                FStar_Syntax_Syntax.Pat_cons uu____15251  in
              FStar_All.pipe_left wrap uu____15250
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
            (fun uu___7_15332  ->
               match uu___7_15332 with
               | (pat,t1) ->
                   let uu____15349 = pack_pat pat  in
                   (uu____15349, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15397 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15397
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15425 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15425
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15471 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15471
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15510 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15510
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15530 =
        bind get
          (fun ps  ->
             let uu____15536 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15536 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15530
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15570 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2177_15577 = ps  in
                 let uu____15578 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2177_15577.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2177_15577.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2177_15577.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2177_15577.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2177_15577.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2177_15577.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2177_15577.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2177_15577.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2177_15577.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2177_15577.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2177_15577.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2177_15577.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15578
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15570
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15605 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15605 with
      | (u,ctx_uvars,g_u) ->
          let uu____15638 = FStar_List.hd ctx_uvars  in
          (match uu____15638 with
           | (ctx_uvar,uu____15652) ->
               let g =
                 let uu____15654 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15654 false
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
        let uu____15677 = goal_of_goal_ty env typ  in
        match uu____15677 with
        | (g,g_u) ->
            let ps =
              let uu____15689 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15692 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15689;
                FStar_Tactics_Types.local_state = uu____15692
              }  in
            let uu____15702 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15702)
  