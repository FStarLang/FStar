open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> normalize [] e t
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu____44 =
      let uu____45 = FStar_Tactics_Types.goal_env g in
      let uu____46 = FStar_Tactics_Types.goal_type g in
      bnorm uu____45 uu____46 in
    FStar_Tactics_Types.goal_with_type g uu____44
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee -> match projectee with | { tac_f;_} -> tac_f
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f -> { tac_f = f }
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t -> fun p -> t.tac_f p
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t ->
    fun p ->
      let uu____160 = FStar_Options.tactics_failhard () in
      if uu____160
      then run t p
      else
        (try (fun uu___31_170 -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____179, msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____183, msg, uu____185) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | e -> FStar_Tactics_Result.Failed (e, p))
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps -> fun f -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
let ret : 'a . 'a -> 'a tac =
  fun x -> mk_tac (fun p -> FStar_Tactics_Result.Success (x, p))
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1 ->
    fun t2 ->
      mk_tac
        (fun p ->
           let uu____265 = run t1 p in
           match uu____265 with
           | FStar_Tactics_Result.Success (a, q) ->
               let uu____272 = t2 a in run uu____272 q
           | FStar_Tactics_Result.Failed (msg, q) ->
               FStar_Tactics_Result.Failed (msg, q))
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p -> FStar_Tactics_Result.Success (p, p))
let (idtac : unit tac) = ret ()
let (get_uvar_solved :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv ->
    let uu____295 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head in
    match uu____295 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g ->
    let uu____317 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar in
    let uu____319 =
      let uu____321 = check_goal_solved g in
      match uu____321 with
      | FStar_Pervasives_Native.None -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____327 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____327 in
    FStar_Util.format2 "%s%s\n" uu____317 uu____319
let (unshadow :
  FStar_Reflection_Data.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Reflection_Data.binders * FStar_Syntax_Syntax.term))
  =
  fun bs ->
    fun t ->
      let s b = (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      let sset bv s1 =
        FStar_Syntax_Syntax.gen_bv s1
          (FStar_Pervasives_Native.Some
             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
          bv.FStar_Syntax_Syntax.sort in
      let fresh_until b f =
        let rec aux i =
          let t1 =
            let uu____404 =
              let uu____406 = FStar_Util.string_of_int i in
              Prims.op_Hat "'" uu____406 in
            Prims.op_Hat b uu____404 in
          let uu____409 = f t1 in
          if uu____409 then t1 else aux (i + (Prims.parse_int "1")) in
        let uu____416 = f b in
        if uu____416 then b else aux (Prims.parse_int "0") in
      let rec go seen subst1 bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____521 = FStar_Syntax_Subst.subst subst1 t1 in
            ((FStar_List.rev bs'), uu____521)
        | b::bs2 ->
            let uu____558 = FStar_Syntax_Subst.subst_binders subst1 [b] in
            (match uu____558 with
             | b1::[] ->
                 let uu____602 = b1 in
                 (match uu____602 with
                  | (bv0, q) ->
                      let nbs =
                        fresh_until (s bv0)
                          (fun s1 ->
                             Prims.op_Negation (FStar_List.mem s1 seen)) in
                      let bv = sset bv0 nbs in
                      let b2 = (bv, q) in
                      let uu____643 =
                        let uu____646 =
                          let uu____649 =
                            let uu____650 =
                              let uu____657 =
                                FStar_Syntax_Syntax.bv_to_name bv in
                              (bv0, uu____657) in
                            FStar_Syntax_Syntax.NT uu____650 in
                          [uu____649] in
                        FStar_List.append subst1 uu____646 in
                      go (nbs :: seen) uu____643 bs2 (b2 :: bs') t1)) in
      go [] [] bs [] t
let (goal_to_string :
  Prims.string ->
    (Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      FStar_Tactics_Types.proofstate ->
        FStar_Tactics_Types.goal -> Prims.string)
  =
  fun kind ->
    fun maybe_num ->
      fun ps ->
        fun g ->
          let w =
            let uu____719 = FStar_Options.print_implicits () in
            if uu____719
            then
              let uu____723 = FStar_Tactics_Types.goal_env g in
              let uu____724 = FStar_Tactics_Types.goal_witness g in
              tts uu____723 uu____724
            else
              (let uu____727 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar in
               match uu____727 with
               | FStar_Pervasives_Native.None -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____733 = FStar_Tactics_Types.goal_env g in
                   let uu____734 = FStar_Tactics_Types.goal_witness g in
                   tts uu____733 uu____734) in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None -> ""
            | FStar_Pervasives_Native.Some (i, n1) ->
                let uu____757 = FStar_Util.string_of_int i in
                let uu____759 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 " %s/%s" uu____757 uu____759 in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")") in
          let goal_binders =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders in
          let goal_ty =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
          let uu____783 = unshadow goal_binders goal_ty in
          match uu____783 with
          | (goal_binders1, goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____797 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1 in
                   let uu____800 =
                     let uu____802 = FStar_Tactics_Types.goal_env g in
                     tts uu____802 goal_ty1 in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____797 w uu____800) in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu____829 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____829
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu____854 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____854
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu____886 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____886
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g ->
    let uu____899 =
      let uu____900 = FStar_Tactics_Types.goal_env g in
      let uu____901 = FStar_Tactics_Types.goal_type g in
      FStar_TypeChecker_Normalize.unfold_whnf uu____900 uu____901 in
    FStar_Syntax_Util.un_squash uu____899
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g -> let uu____910 = get_phi g in FStar_Option.isSome uu____910
let (print : Prims.string -> unit tac) = fun msg -> tacprint msg; ret ()
let (debugging : unit -> Prims.bool tac) =
  fun uu____934 ->
    bind get
      (fun ps ->
         let uu____942 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         ret uu____942)
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____957 ->
    match uu____957 with
    | (msg, ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals in
        let n1 = n_active + n_smt in
        let uu____979 =
          let uu____983 =
            let uu____987 =
              let uu____989 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____989
                msg in
            let uu____992 =
              let uu____996 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____1000 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range in
                  FStar_Util.format1 "Location: %s\n" uu____1000
                else "" in
              let uu____1006 =
                let uu____1010 =
                  let uu____1012 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp") in
                  if uu____1012
                  then
                    let uu____1017 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits in
                    FStar_Util.format1 "Imps: %s\n" uu____1017
                  else "" in
                [uu____1010] in
              uu____996 :: uu____1006 in
            uu____987 :: uu____992 in
          let uu____1027 =
            let uu____1031 =
              FStar_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals in
            let uu____1051 =
              FStar_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals in
            FStar_List.append uu____1031 uu____1051 in
          FStar_List.append uu____983 uu____1027 in
        FStar_String.concat "" uu____979
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders in
    let g_type = FStar_Tactics_Types.goal_type g in
    let uu____1090 = unshadow g_binders g_type in
    match uu____1090 with
    | (g_binders1, g_type1) ->
        let j_binders =
          let uu____1098 =
            let uu____1099 = FStar_Tactics_Types.goal_env g in
            FStar_TypeChecker_Env.dsenv uu____1099 in
          FStar_Syntax_Print.binders_to_json uu____1098 g_binders1 in
        let uu____1100 =
          let uu____1108 =
            let uu____1116 =
              let uu____1122 =
                let uu____1123 =
                  let uu____1131 =
                    let uu____1137 =
                      let uu____1138 =
                        let uu____1140 = FStar_Tactics_Types.goal_env g in
                        let uu____1141 = FStar_Tactics_Types.goal_witness g in
                        tts uu____1140 uu____1141 in
                      FStar_Util.JsonStr uu____1138 in
                    ("witness", uu____1137) in
                  let uu____1144 =
                    let uu____1152 =
                      let uu____1158 =
                        let uu____1159 =
                          let uu____1161 = FStar_Tactics_Types.goal_env g in
                          tts uu____1161 g_type1 in
                        FStar_Util.JsonStr uu____1159 in
                      ("type", uu____1158) in
                    [uu____1152;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))] in
                  uu____1131 :: uu____1144 in
                FStar_Util.JsonAssoc uu____1123 in
              ("goal", uu____1122) in
            [uu____1116] in
          ("hyps", j_binders) :: uu____1108 in
        FStar_Util.JsonAssoc uu____1100
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____1215 ->
    match uu____1215 with
    | (msg, ps) ->
        let uu____1225 =
          let uu____1233 =
            let uu____1241 =
              let uu____1249 =
                let uu____1257 =
                  let uu____1263 =
                    let uu____1264 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals in
                    FStar_Util.JsonList uu____1264 in
                  ("goals", uu____1263) in
                let uu____1269 =
                  let uu____1277 =
                    let uu____1283 =
                      let uu____1284 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals in
                      FStar_Util.JsonList uu____1284 in
                    ("smt-goals", uu____1283) in
                  [uu____1277] in
                uu____1257 :: uu____1269 in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____1249 in
            ("label", (FStar_Util.JsonStr msg)) :: uu____1241 in
          let uu____1318 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____1334 =
                let uu____1340 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range in
                ("location", uu____1340) in
              [uu____1334]
            else [] in
          FStar_List.append uu____1233 uu____1318 in
        FStar_Util.JsonAssoc uu____1225
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps ->
    fun msg ->
      FStar_Options.with_saved_options
        (fun uu____1380 ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
let (print_proof_state : Prims.string -> unit tac) =
  fun msg ->
    mk_tac
      (fun ps ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc in
         (let uu____1411 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____1411 msg);
         FStar_Tactics_Result.Success ((), ps))
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f -> fun cont -> bind get (fun ps -> log ps f; cont ())
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStar_Tactics_Result.Failed (e, ps))
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu____1484 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____1484
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
let fail1 : 'Auu____1498 . Prims.string -> Prims.string -> 'Auu____1498 tac =
  fun msg ->
    fun x -> let uu____1515 = FStar_Util.format1 msg x in fail uu____1515
let fail2 :
  'Auu____1526 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1526 tac
  =
  fun msg ->
    fun x ->
      fun y -> let uu____1550 = FStar_Util.format2 msg x y in fail uu____1550
let fail3 :
  'Auu____1563 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1563 tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____1594 = FStar_Util.format3 msg x y z in fail uu____1594
let fail4 :
  'Auu____1609 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1609 tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____1647 = FStar_Util.format4 msg x y z w in
            fail uu____1647
let catch : 'a . 'a tac -> (Prims.exn, 'a) FStar_Util.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____1682 = run t ps in
         match uu____1682 with
         | FStar_Tactics_Result.Success (a, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___227_1706 = ps in
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
                 } in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
let recover : 'a . 'a tac -> (Prims.exn, 'a) FStar_Util.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let uu____1745 = run t ps in
         match uu____1745 with
         | FStar_Tactics_Result.Success (a, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t ->
    let uu____1793 = catch t in
    bind uu____1793
      (fun r ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1820 -> ret FStar_Pervasives_Native.None)
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t ->
    mk_tac
      (fun ps ->
         try
           (fun uu___253_1852 ->
              match () with
              | () -> let uu____1857 = trytac t in run uu____1857 ps) ()
         with
         | FStar_Errors.Err (uu____1873, msg) ->
             (log ps
                (fun uu____1879 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1885, msg, uu____1887) ->
             (log ps
                (fun uu____1892 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      mk_tac
        (fun ps ->
           let uu____1929 = run t ps in
           match uu____1929 with
           | FStar_Tactics_Result.Success (a, q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg, q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e, q) ->
               FStar_Tactics_Result.Failed (e, q))
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p -> mk_tac (fun uu____1953 -> FStar_Tactics_Result.Success ((), p))
let (add_implicits : implicits -> unit tac) =
  fun i ->
    bind get
      (fun p ->
         set
           (let uu___288_1968 = p in
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
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____1992 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
         if uu____1992
         then
           let uu____1996 = FStar_Syntax_Print.term_to_string t1 in
           let uu____1998 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1996
             uu____1998
         else ());
        (try
           (fun uu___296_2009 ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2 in
                  ((let uu____2017 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346") in
                    if uu____2017
                    then
                      let uu____2021 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res in
                      let uu____2023 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____2025 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____2021
                        uu____2023 uu____2025
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____2036 =
                          add_implicits g.FStar_TypeChecker_Env.implicits in
                        bind uu____2036 (fun uu____2041 -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____2051, msg) ->
             mlog
               (fun uu____2057 ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____2060 -> ret false)
         | FStar_Errors.Error (uu____2063, msg, r) ->
             mlog
               (fun uu____2071 ->
                  let uu____2072 = FStar_Range.string_of_range r in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____2072) (fun uu____2076 -> ret false))
let (compress_implicits : unit tac) =
  bind get
    (fun ps ->
       let imps = ps.FStar_Tactics_Types.all_implicits in
       let g =
         let uu___322_2090 = FStar_TypeChecker_Env.trivial_guard in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___322_2090.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___322_2090.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___322_2090.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         } in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g in
       let ps' =
         let uu___326_2093 = ps in
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
         } in
       set ps')
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        bind idtac
          (fun uu____2120 ->
             (let uu____2122 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
              if uu____2122
              then
                (FStar_Options.push ();
                 (let uu____2127 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck" in
                  ()))
              else ());
             (let uu____2131 = __do_unify env t1 t2 in
              bind uu____2131
                (fun r ->
                   (let uu____2142 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346") in
                    if uu____2142 then FStar_Options.pop () else ());
                   ret r)))
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps ->
       let ps' =
         let uu___341_2156 = ps in
         let uu____2157 =
           FStar_List.filter
             (fun g ->
                let uu____2163 = check_goal_solved g in
                FStar_Option.isNone uu____2163) ps.FStar_Tactics_Types.goals in
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
         } in
       set ps')
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal ->
    fun solution ->
      let uu____2181 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____2181 with
      | FStar_Pervasives_Native.Some uu____2186 ->
          let uu____2187 =
            let uu____2189 = goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____2189 in
          fail uu____2187
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal ->
    fun solution ->
      let uu____2210 = FStar_Tactics_Types.goal_env goal in
      let uu____2211 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____2210 solution uu____2211
let (__dismiss : unit tac) =
  bind get
    (fun p ->
       let uu____2218 =
         let uu___354_2219 = p in
         let uu____2220 = FStar_List.tl p.FStar_Tactics_Types.goals in
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
         } in
       set uu____2218)
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      mlog
        (fun uu____2242 ->
           let uu____2243 =
             let uu____2245 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____2245 in
           let uu____2246 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____2243 uu____2246)
        (fun uu____2251 ->
           let uu____2252 = trysolve goal solution in
           bind uu____2252
             (fun b ->
                if b
                then bind __dismiss (fun uu____2264 -> remove_solved_goals)
                else
                  (let uu____2267 =
                     let uu____2269 =
                       let uu____2271 = FStar_Tactics_Types.goal_env goal in
                       tts uu____2271 solution in
                     let uu____2272 =
                       let uu____2274 = FStar_Tactics_Types.goal_env goal in
                       let uu____2275 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____2274 uu____2275 in
                     let uu____2276 =
                       let uu____2278 = FStar_Tactics_Types.goal_env goal in
                       let uu____2279 = FStar_Tactics_Types.goal_type goal in
                       tts uu____2278 uu____2279 in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____2269 uu____2272 uu____2276 in
                   fail uu____2267)))
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal ->
    fun solution ->
      let uu____2296 = set_solution goal solution in
      bind uu____2296
        (fun uu____2300 ->
           bind __dismiss (fun uu____2302 -> remove_solved_goals))
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___370_2321 = ps in
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
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___374_2340 = ps in
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
  fun g ->
    let uu____2356 = FStar_Options.defensive () in
    if uu____2356
    then
      let b = true in
      let env = FStar_Tactics_Types.goal_env g in
      let b1 =
        b &&
          (let uu____2366 = FStar_Tactics_Types.goal_witness g in
           FStar_TypeChecker_Env.closed env uu____2366) in
      let b2 =
        b1 &&
          (let uu____2370 = FStar_Tactics_Types.goal_type g in
           FStar_TypeChecker_Env.closed env uu____2370) in
      let rec aux b3 e =
        let uu____2385 = FStar_TypeChecker_Env.pop_bv e in
        match uu____2385 with
        | FStar_Pervasives_Native.None -> b3
        | FStar_Pervasives_Native.Some (bv, e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
            aux b4 e1 in
      let uu____2405 =
        (let uu____2409 = aux b2 env in Prims.op_Negation uu____2409) &&
          (let uu____2412 = FStar_ST.op_Bang nwarn in
           uu____2412 < (Prims.parse_int "5")) in
      (if uu____2405
       then
         ((let uu____2438 =
             let uu____2439 = FStar_Tactics_Types.goal_type g in
             uu____2439.FStar_Syntax_Syntax.pos in
           let uu____2442 =
             let uu____2448 =
               let uu____2450 = goal_to_string_verbose g in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2450 in
             (FStar_Errors.Warning_IllFormedGoal, uu____2448) in
           FStar_Errors.log_issue uu____2438 uu____2442);
          (let uu____2454 =
             let uu____2456 = FStar_ST.op_Bang nwarn in
             uu____2456 + (Prims.parse_int "1") in
           FStar_ST.op_Colon_Equals nwarn uu____2454))
       else ())
    else ()
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun p ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___396_2525 = p in
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
  fun gs ->
    bind get
      (fun p ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___401_2546 = p in
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
  fun gs ->
    bind get
      (fun p ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___406_2567 = p in
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
  fun gs ->
    bind get
      (fun p ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___411_2588 = p in
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
  fun g -> bind __dismiss (fun uu____2600 -> add_goals [g])
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason ->
    fun env ->
      fun typ ->
        let uu____2631 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
        match uu____2631 with
        | (u, ctx_uvar, g_u) ->
            let uu____2669 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____2669
              (fun uu____2678 ->
                 let uu____2679 =
                   let uu____2684 =
                     let uu____2685 = FStar_List.hd ctx_uvar in
                     FStar_Pervasives_Native.fst uu____2685 in
                   (u, uu____2684) in
                 ret uu____2679)
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2706 = FStar_Syntax_Util.un_squash t1 in
    match uu____2706 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____2718 =
          let uu____2719 = FStar_Syntax_Subst.compress t'1 in
          uu____2719.FStar_Syntax_Syntax.n in
        (match uu____2718 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2724 -> false)
    | uu____2726 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2739 = FStar_Syntax_Util.un_squash t in
    match uu____2739 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2750 =
          let uu____2751 = FStar_Syntax_Subst.compress t' in
          uu____2751.FStar_Syntax_Syntax.n in
        (match uu____2750 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2756 -> false)
    | uu____2758 -> false
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2771 ->
    bind get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2783 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
             (match uu____2783 with
              | FStar_Pervasives_Native.None -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2790 = goal_to_string_verbose hd1 in
                    let uu____2792 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2790 uu____2792);
                   ret hd1)))
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t ->
    let uu____2805 =
      bind get
        (fun ps ->
           let uu____2811 = cur_goal () in
           bind uu____2811
             (fun g ->
                (let uu____2818 =
                   let uu____2819 = FStar_Tactics_Types.goal_type g in
                   uu____2819.FStar_Syntax_Syntax.pos in
                 let uu____2822 =
                   let uu____2828 =
                     let uu____2830 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2830 in
                   (FStar_Errors.Warning_TacAdmit, uu____2828) in
                 FStar_Errors.log_issue uu____2818 uu____2822);
                solve' g t)) in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2805
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2853 ->
    bind get
      (fun ps ->
         let n1 = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___456_2864 = ps in
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
           } in
         let uu____2866 = set ps1 in
         bind uu____2866
           (fun uu____2871 ->
              let uu____2872 = FStar_BigInt.of_int_fs n1 in ret uu____2872))
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label1 ->
            let typ =
              let uu____2910 = env.FStar_TypeChecker_Env.universe_of env phi in
              FStar_Syntax_Util.mk_squash uu____2910 phi in
            let uu____2911 = new_uvar reason env typ in
            bind uu____2911
              (fun uu____2926 ->
                 match uu____2926 with
                 | (uu____2933, ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1 in
                     ret goal)
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e ->
    fun t ->
      bind get
        (fun ps ->
           mlog
             (fun uu____2980 ->
                let uu____2981 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2981)
             (fun uu____2986 ->
                let e1 =
                  let uu___474_2988 = e in
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
                  } in
                try
                  (fun uu___478_3000 ->
                     match () with
                     | () ->
                         let uu____3009 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         ret uu____3009) ()
                with
                | FStar_Errors.Err (uu____3036, msg) ->
                    let uu____3040 = tts e1 t in
                    let uu____3042 =
                      let uu____3044 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____3044
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3040 uu____3042 msg
                | FStar_Errors.Error (uu____3054, msg, uu____3056) ->
                    let uu____3059 = tts e1 t in
                    let uu____3061 =
                      let uu____3063 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____3063
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3059 uu____3061 msg))
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e ->
    fun t ->
      bind get
        (fun ps ->
           mlog
             (fun uu____3116 ->
                let uu____3117 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3117)
             (fun uu____3122 ->
                let e1 =
                  let uu___495_3124 = e in
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
                  } in
                try
                  (fun uu___499_3139 ->
                     match () with
                     | () ->
                         let uu____3148 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____3148 with
                          | (t1, lc, g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3186, msg) ->
                    let uu____3190 = tts e1 t in
                    let uu____3192 =
                      let uu____3194 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____3194
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3190 uu____3192 msg
                | FStar_Errors.Error (uu____3204, msg, uu____3206) ->
                    let uu____3209 = tts e1 t in
                    let uu____3211 =
                      let uu____3213 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____3213
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3209 uu____3211 msg))
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e ->
    fun t ->
      bind get
        (fun ps ->
           mlog
             (fun uu____3266 ->
                let uu____3267 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3267)
             (fun uu____3273 ->
                let e1 =
                  let uu___520_3275 = e in
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
                  } in
                let e2 =
                  let uu___523_3278 = e1 in
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
                  } in
                try
                  (fun uu___527_3290 ->
                     match () with
                     | () ->
                         let uu____3299 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         ret uu____3299) ()
                with
                | FStar_Errors.Err (uu____3326, msg) ->
                    let uu____3330 = tts e2 t in
                    let uu____3332 =
                      let uu____3334 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____3334
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3330 uu____3332 msg
                | FStar_Errors.Error (uu____3344, msg, uu____3346) ->
                    let uu____3349 = tts e2 t in
                    let uu____3351 =
                      let uu____3353 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____3353
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3349 uu____3351 msg))
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta] in
      let t1 = normalize steps e t in is_true t1
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____3387 ->
    bind get (fun ps -> ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol ->
    bind get
      (fun ps ->
         set
           (let uu___548_3406 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___548_3406.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___548_3406.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___548_3406.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___548_3406.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___548_3406.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___548_3406.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___548_3406.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___548_3406.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___548_3406.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___548_3406.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___548_3406.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___548_3406.FStar_Tactics_Types.local_state)
            }))
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol ->
    fun t ->
      let uu____3431 = get_guard_policy () in
      bind uu____3431
        (fun old_pol ->
           let uu____3437 = set_guard_policy pol in
           bind uu____3437
             (fun uu____3441 ->
                bind t
                  (fun r ->
                     let uu____3445 = set_guard_policy old_pol in
                     bind uu____3445 (fun uu____3449 -> ret r))))
let (getopts : FStar_Options.optionstate tac) =
  let uu____3453 = let uu____3458 = cur_goal () in trytac uu____3458 in
  bind uu____3453
    (fun uu___0_3465 ->
       match uu___0_3465 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____3471 = FStar_Options.peek () in ret uu____3471)
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason ->
    fun e ->
      fun g ->
        mlog
          (fun uu____3496 ->
             let uu____3497 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3497)
          (fun uu____3502 ->
             let uu____3503 = add_implicits g.FStar_TypeChecker_Env.implicits in
             bind uu____3503
               (fun uu____3507 ->
                  bind getopts
                    (fun opts ->
                       let uu____3511 =
                         let uu____3512 =
                           FStar_TypeChecker_Rel.simplify_guard e g in
                         uu____3512.FStar_TypeChecker_Env.guard_f in
                       match uu____3511 with
                       | FStar_TypeChecker_Common.Trivial -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3516 = istrivial e f in
                           if uu____3516
                           then ret ()
                           else
                             bind get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu____3529 =
                                          let uu____3535 =
                                            let uu____3537 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3537 in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3535) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3529);
                                       ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      mlog
                                        (fun uu____3543 ->
                                           let uu____3544 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3544)
                                        (fun uu____3549 ->
                                           let uu____3550 =
                                             mk_irrelevant_goal reason e f
                                               opts "" in
                                           bind uu____3550
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___577_3558 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___577_3558.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___577_3558.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___577_3558.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___577_3558.FStar_Tactics_Types.label)
                                                  } in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT ->
                                      mlog
                                        (fun uu____3562 ->
                                           let uu____3563 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3563)
                                        (fun uu____3568 ->
                                           let uu____3569 =
                                             mk_irrelevant_goal reason e f
                                               opts "" in
                                           bind uu____3569
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___584_3577 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___584_3577.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___584_3577.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___584_3577.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___584_3577.FStar_Tactics_Types.label)
                                                  } in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force ->
                                      mlog
                                        (fun uu____3581 ->
                                           let uu____3582 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3582)
                                        (fun uu____3586 ->
                                           try
                                             (fun uu___591_3591 ->
                                                match () with
                                                | () ->
                                                    let uu____3594 =
                                                      let uu____3596 =
                                                        let uu____3598 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3598 in
                                                      Prims.op_Negation
                                                        uu____3596 in
                                                    if uu____3594
                                                    then
                                                      mlog
                                                        (fun uu____3605 ->
                                                           let uu____3606 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3606)
                                                        (fun uu____3610 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___590_3615 ->
                                               mlog
                                                 (fun uu____3620 ->
                                                    let uu____3621 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3621)
                                                 (fun uu____3625 ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t ->
    let uu____3637 =
      let uu____3640 = cur_goal () in
      bind uu____3640
        (fun goal ->
           let uu____3646 =
             let uu____3655 = FStar_Tactics_Types.goal_env goal in
             __tc_lax uu____3655 t in
           bind uu____3646
             (fun uu____3667 ->
                match uu____3667 with
                | (uu____3676, lc, uu____3678) ->
                    let uu____3679 = FStar_Syntax_Syntax.lcomp_comp lc in
                    ret uu____3679)) in
    FStar_All.pipe_left (wrap_err "tcc") uu____3637
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t ->
    let uu____3695 =
      let uu____3700 = tcc t in
      bind uu____3700 (fun c -> ret (FStar_Syntax_Util.comp_result c)) in
    FStar_All.pipe_left (wrap_err "tc") uu____3695
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label1 ->
            let uu____3752 = mk_irrelevant_goal reason env phi opts label1 in
            bind uu____3752 (fun goal -> add_goals [goal])
let (trivial : unit -> unit tac) =
  fun uu____3764 ->
    let uu____3767 = cur_goal () in
    bind uu____3767
      (fun goal ->
         let uu____3773 =
           let uu____3775 = FStar_Tactics_Types.goal_env goal in
           let uu____3776 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____3775 uu____3776 in
         if uu____3773
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3782 =
              let uu____3784 = FStar_Tactics_Types.goal_env goal in
              let uu____3785 = FStar_Tactics_Types.goal_type goal in
              tts uu____3784 uu____3785 in
            fail1 "Not a trivial goal: %s" uu____3782))
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1 ->
    fun l ->
      fun r ->
        bind get
          (fun p ->
             let uu____3836 =
               try
                 (fun uu___649_3859 ->
                    match () with
                    | () ->
                        let uu____3870 =
                          let uu____3879 = FStar_BigInt.to_int_fs n1 in
                          FStar_List.splitAt uu____3879
                            p.FStar_Tactics_Types.goals in
                        ret uu____3870) ()
               with | uu___648_3890 -> fail "divide: not enough goals" in
             bind uu____3836
               (fun uu____3927 ->
                  match uu____3927 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___631_3953 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___631_3953.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___631_3953.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___631_3953.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___631_3953.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___631_3953.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___631_3953.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___631_3953.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___631_3953.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___631_3953.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___631_3953.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___631_3953.FStar_Tactics_Types.local_state)
                        } in
                      let uu____3954 = set lp in
                      bind uu____3954
                        (fun uu____3962 ->
                           bind l
                             (fun a ->
                                bind get
                                  (fun lp' ->
                                     let rp =
                                       let uu___637_3978 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___637_3978.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___637_3978.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___637_3978.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___637_3978.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___637_3978.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___637_3978.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___637_3978.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___637_3978.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___637_3978.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___637_3978.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___637_3978.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____3979 = set rp in
                                     bind uu____3979
                                       (fun uu____3987 ->
                                          bind r
                                            (fun b ->
                                               bind get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___643_4003 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___643_4003.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___643_4003.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____4004 = set p' in
                                                    bind uu____4004
                                                      (fun uu____4012 ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4018 ->
                                                              ret (a, b)))))))))))
let focus : 'a . 'a tac -> 'a tac =
  fun f ->
    let uu____4040 = divide FStar_BigInt.one f idtac in
    bind uu____4040
      (fun uu____4053 -> match uu____4053 with | (a, ()) -> ret a)
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau ->
    bind get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4091::uu____4092 ->
             let uu____4095 =
               let uu____4104 = map tau in
               divide FStar_BigInt.one tau uu____4104 in
             bind uu____4095
               (fun uu____4122 ->
                  match uu____4122 with | (h, t) -> ret (h :: t)))
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1 ->
    fun t2 ->
      let uu____4164 =
        bind t1
          (fun uu____4169 ->
             let uu____4170 = map t2 in
             bind uu____4170 (fun uu____4178 -> ret ())) in
      focus uu____4164
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4188 ->
    let uu____4191 =
      let uu____4194 = cur_goal () in
      bind uu____4194
        (fun goal ->
           let uu____4203 =
             let uu____4210 = FStar_Tactics_Types.goal_type goal in
             FStar_Syntax_Util.arrow_one uu____4210 in
           match uu____4203 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____4219 =
                 let uu____4221 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____4221 in
               if uu____4219
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4230 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____4230 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____4246 = new_uvar "intro" env' typ' in
                  bind uu____4246
                    (fun uu____4263 ->
                       match uu____4263 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____4287 = set_solution goal sol in
                           bind uu____4287
                             (fun uu____4293 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____4295 =
                                  let uu____4298 = bnorm_goal g in
                                  replace_cur uu____4298 in
                                bind uu____4295 (fun uu____4300 -> ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____4305 =
                 let uu____4307 = FStar_Tactics_Types.goal_env goal in
                 let uu____4308 = FStar_Tactics_Types.goal_type goal in
                 tts uu____4307 uu____4308 in
               fail1 "goal is not an arrow (%s)" uu____4305) in
    FStar_All.pipe_left (wrap_err "intro") uu____4191
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4326 ->
    let uu____4333 = cur_goal () in
    bind uu____4333
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4352 =
            let uu____4359 = FStar_Tactics_Types.goal_type goal in
            FStar_Syntax_Util.arrow_one uu____4359 in
          match uu____4352 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____4372 =
                let uu____4374 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____4374 in
              if uu____4372
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4391 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4391 in
                 let bs =
                   let uu____4402 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____4402; b] in
                 let env' =
                   let uu____4428 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____4428 bs in
                 let uu____4429 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 bind uu____4429
                   (fun uu____4455 ->
                      match uu____4455 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____4469 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____4472 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4469
                              FStar_Parser_Const.effect_Tot_lid uu____4472 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____4490 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____4490 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____4512 =
                                   let uu____4513 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____4513.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4512 in
                               let uu____4529 = set_solution goal tm in
                               bind uu____4529
                                 (fun uu____4538 ->
                                    let uu____4539 =
                                      let uu____4542 =
                                        bnorm_goal
                                          (let uu___714_4545 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___714_4545.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___714_4545.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___714_4545.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___714_4545.FStar_Tactics_Types.label)
                                           }) in
                                      replace_cur uu____4542 in
                                    bind uu____4539
                                      (fun uu____4552 ->
                                         let uu____4553 =
                                           let uu____4558 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____4558, b) in
                                         ret uu____4553)))))
          | FStar_Pervasives_Native.None ->
              let uu____4567 =
                let uu____4569 = FStar_Tactics_Types.goal_env goal in
                let uu____4570 = FStar_Tactics_Types.goal_type goal in
                tts uu____4569 uu____4570 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4567))
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s ->
    let uu____4590 = cur_goal () in
    bind uu____4590
      (fun goal ->
         mlog
           (fun uu____4597 ->
              let uu____4598 =
                let uu____4600 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____4600 in
              FStar_Util.print1 "norm: witness = %s\n" uu____4598)
           (fun uu____4606 ->
              let steps =
                let uu____4610 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4610 in
              let t =
                let uu____4614 = FStar_Tactics_Types.goal_env goal in
                let uu____4615 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____4614 uu____4615 in
              let uu____4616 = FStar_Tactics_Types.goal_with_type goal t in
              replace_cur uu____4616))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____4641 =
          bind get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4649 -> g.FStar_Tactics_Types.opts
                 | uu____4652 -> FStar_Options.peek () in
               mlog
                 (fun uu____4657 ->
                    let uu____4658 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4658)
                 (fun uu____4663 ->
                    let uu____4664 = __tc_lax e t in
                    bind uu____4664
                      (fun uu____4685 ->
                         match uu____4685 with
                         | (t1, uu____4695, uu____4696) ->
                             let steps =
                               let uu____4700 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4700 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             mlog
                               (fun uu____4706 ->
                                  let uu____4707 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4707)
                               (fun uu____4711 -> ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4641
let (refine_intro : unit -> unit tac) =
  fun uu____4724 ->
    let uu____4727 =
      let uu____4730 = cur_goal () in
      bind uu____4730
        (fun g ->
           let uu____4737 =
             let uu____4748 = FStar_Tactics_Types.goal_env g in
             let uu____4749 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____4748 uu____4749 in
           match uu____4737 with
           | (uu____4752, FStar_Pervasives_Native.None) ->
               fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____4778 =
                 let uu____4783 =
                   let uu____4788 =
                     let uu____4789 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____4789] in
                   FStar_Syntax_Subst.open_term uu____4788 phi in
                 match uu____4783 with
                 | (bvs, phi1) ->
                     let uu____4814 =
                       let uu____4815 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____4815 in
                     (uu____4814, phi1) in
               (match uu____4778 with
                | (bv1, phi1) ->
                    let uu____4834 =
                      let uu____4837 = FStar_Tactics_Types.goal_env g in
                      let uu____4838 =
                        let uu____4839 =
                          let uu____4842 =
                            let uu____4843 =
                              let uu____4850 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____4850) in
                            FStar_Syntax_Syntax.NT uu____4843 in
                          [uu____4842] in
                        FStar_Syntax_Subst.subst uu____4839 phi1 in
                      mk_irrelevant_goal "refine_intro refinement" uu____4837
                        uu____4838 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    bind uu____4834
                      (fun g2 ->
                         bind __dismiss
                           (fun uu____4859 -> add_goals [g1; g2])))) in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4727
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1 ->
    fun t ->
      let uu____4882 = cur_goal () in
      bind uu____4882
        (fun goal ->
           let env =
             if set_expected_typ1
             then
               let uu____4891 = FStar_Tactics_Types.goal_env goal in
               let uu____4892 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____4891 uu____4892
             else FStar_Tactics_Types.goal_env goal in
           let uu____4895 = __tc env t in
           bind uu____4895
             (fun uu____4914 ->
                match uu____4914 with
                | (t1, typ, guard) ->
                    mlog
                      (fun uu____4929 ->
                         let uu____4930 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____4932 =
                           let uu____4934 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____4934
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4930 uu____4932)
                      (fun uu____4938 ->
                         let uu____4939 =
                           let uu____4942 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____4942 guard in
                         bind uu____4939
                           (fun uu____4945 ->
                              mlog
                                (fun uu____4949 ->
                                   let uu____4950 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____4952 =
                                     let uu____4954 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4954 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4950 uu____4952)
                                (fun uu____4958 ->
                                   let uu____4959 =
                                     let uu____4963 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____4964 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____4963 typ uu____4964 in
                                   bind uu____4959
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4974 =
                                             let uu____4976 =
                                               FStar_Tactics_Types.goal_env
                                                 goal in
                                             tts uu____4976 t1 in
                                           let uu____4977 =
                                             let uu____4979 =
                                               FStar_Tactics_Types.goal_env
                                                 goal in
                                             tts uu____4979 typ in
                                           let uu____4980 =
                                             let uu____4982 =
                                               FStar_Tactics_Types.goal_env
                                                 goal in
                                             let uu____4983 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             tts uu____4982 uu____4983 in
                                           let uu____4984 =
                                             let uu____4986 =
                                               FStar_Tactics_Types.goal_env
                                                 goal in
                                             let uu____4987 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal in
                                             tts uu____4986 uu____4987 in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4974 uu____4977 uu____4980
                                             uu____4984)))))))
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine ->
    fun set_expected_typ1 ->
      fun tm ->
        let uu____5013 =
          mlog
            (fun uu____5018 ->
               let uu____5019 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5019)
            (fun uu____5024 ->
               let uu____5025 =
                 let uu____5032 = __exact_now set_expected_typ1 tm in
                 catch uu____5032 in
               bind uu____5025
                 (fun uu___2_5041 ->
                    match uu___2_5041 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5052 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5056 ->
                             let uu____5057 =
                               let uu____5064 =
                                 let uu____5067 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 bind uu____5067
                                   (fun uu____5072 ->
                                      let uu____5073 = refine_intro () in
                                      bind uu____5073
                                        (fun uu____5077 ->
                                           __exact_now set_expected_typ1 tm)) in
                               catch uu____5064 in
                             bind uu____5057
                               (fun uu___1_5084 ->
                                  match uu___1_5084 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5093 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5096 -> ret ())
                                  | FStar_Util.Inl uu____5097 ->
                                      mlog
                                        (fun uu____5099 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5102 -> traise e))))) in
        FStar_All.pipe_left (wrap_err "exact") uu____5013
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f ->
    fun l ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5154 = f x in
          bind uu____5154
            (fun y ->
               let uu____5162 = mapM f xs in
               bind uu____5162 (fun ys -> ret (y :: ys)))
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
    FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun acc ->
    fun e ->
      fun ty1 ->
        fun ty2 ->
          let uu____5234 = do_unify e ty1 ty2 in
          bind uu____5234
            (fun uu___3_5248 ->
               if uu___3_5248
               then ret acc
               else
                 (let uu____5268 = FStar_Syntax_Util.arrow_one ty1 in
                  match uu____5268 with
                  | FStar_Pervasives_Native.None ->
                      let uu____5289 = FStar_Syntax_Print.term_to_string ty1 in
                      let uu____5291 = FStar_Syntax_Print.term_to_string ty2 in
                      fail2 "Could not instantiate, %s to %s" uu____5289
                        uu____5291
                  | FStar_Pervasives_Native.Some (b, c) ->
                      let uu____5308 =
                        let uu____5310 = FStar_Syntax_Util.is_total_comp c in
                        Prims.op_Negation uu____5310 in
                      if uu____5308
                      then fail "Codomain is effectful"
                      else
                        (let uu____5334 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                         bind uu____5334
                           (fun uu____5361 ->
                              match uu____5361 with
                              | (uvt, uv) ->
                                  let typ = FStar_Syntax_Util.comp_result c in
                                  let typ' =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT
                                         ((FStar_Pervasives_Native.fst b),
                                           uvt)] typ in
                                  __try_match_by_application
                                    ((uvt, (FStar_Pervasives_Native.snd b),
                                       uv) :: acc) e typ' ty2))))
let (try_match_by_application :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
          FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  = fun e -> fun ty1 -> fun ty2 -> __try_match_by_application [] e ty1 ty2
let (t_apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt ->
    fun tm ->
      let uu____5453 =
        mlog
          (fun uu____5458 ->
             let uu____5459 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5459)
          (fun uu____5464 ->
             let uu____5465 = cur_goal () in
             bind uu____5465
               (fun goal ->
                  let e = FStar_Tactics_Types.goal_env goal in
                  let uu____5473 = __tc e tm in
                  bind uu____5473
                    (fun uu____5494 ->
                       match uu____5494 with
                       | (tm1, typ, guard) ->
                           let typ1 = bnorm e typ in
                           let uu____5507 =
                             let uu____5518 =
                               FStar_Tactics_Types.goal_type goal in
                             try_match_by_application e typ1 uu____5518 in
                           bind uu____5507
                             (fun uvs ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____5556)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____5560 -> q in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5583 ->
                                       fun w ->
                                         match uu____5583 with
                                         | (uvt, q, uu____5601) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1 in
                                let uvset =
                                  let uu____5633 =
                                    FStar_Syntax_Free.new_uv_set () in
                                  FStar_List.fold_right
                                    (fun uu____5650 ->
                                       fun s ->
                                         match uu____5650 with
                                         | (uu____5662, uu____5663, uv) ->
                                             let uu____5665 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                             FStar_Util.set_union s
                                               uu____5665) uvs uu____5633 in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset in
                                let uu____5675 = solve' goal w in
                                bind uu____5675
                                  (fun uu____5680 ->
                                     let uu____5681 =
                                       mapM
                                         (fun uu____5698 ->
                                            match uu____5698 with
                                            | (uvt, q, uv) ->
                                                let uu____5710 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                (match uu____5710 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5715 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     let uu____5716 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv) in
                                                     if uu____5716
                                                     then ret ()
                                                     else
                                                       (let uu____5723 =
                                                          let uu____5726 =
                                                            bnorm_goal
                                                              (let uu___875_5729
                                                                 = goal in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___875_5729.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___875_5729.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___875_5729.FStar_Tactics_Types.label)
                                                               }) in
                                                          [uu____5726] in
                                                        add_goals uu____5723)))
                                         uvs in
                                     bind uu____5681
                                       (fun uu____5734 ->
                                          proc_guard "apply guard" e guard)))))) in
      FStar_All.pipe_left (wrap_err "apply") uu____5453
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____5762 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____5762
    then
      let uu____5771 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5786 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5839 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____5771 with
      | (pre, post) ->
          let post1 =
            let uu____5872 =
              let uu____5883 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____5883] in
            FStar_Syntax_Util.mk_app post uu____5872 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5914 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name in
       if uu____5914
       then
         let uu____5923 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____5923
           (fun post -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b . ('a -> 'b -> 'b tac) -> 'b -> 'a Prims.list -> 'b tac =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> ret e
        | x::xs1 ->
            let uu____6002 = f x e in
            bind uu____6002 (fun e' -> fold_left f e' xs1)
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm ->
    let uu____6017 =
      let uu____6020 =
        bind get
          (fun ps ->
             mlog
               (fun uu____6027 ->
                  let uu____6028 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6028)
               (fun uu____6034 ->
                  let is_unit_t t =
                    let uu____6042 =
                      let uu____6043 = FStar_Syntax_Subst.compress t in
                      uu____6043.FStar_Syntax_Syntax.n in
                    match uu____6042 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6049 -> false in
                  let uu____6051 = cur_goal () in
                  bind uu____6051
                    (fun goal ->
                       let uu____6057 =
                         let uu____6066 = FStar_Tactics_Types.goal_env goal in
                         __tc uu____6066 tm in
                       bind uu____6057
                         (fun uu____6081 ->
                            match uu____6081 with
                            | (tm1, t, guard) ->
                                let uu____6093 =
                                  FStar_Syntax_Util.arrow_formals_comp t in
                                (match uu____6093 with
                                 | (bs, comp) ->
                                     let uu____6126 = lemma_or_sq comp in
                                     (match uu____6126 with
                                      | FStar_Pervasives_Native.None ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre, post) ->
                                          let uu____6146 =
                                            fold_left
                                              (fun uu____6208 ->
                                                 fun uu____6209 ->
                                                   match (uu____6208,
                                                           uu____6209)
                                                   with
                                                   | ((b, aq),
                                                      (uvs, imps, subst1)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort in
                                                       let uu____6360 =
                                                         is_unit_t b_t in
                                                       if uu____6360
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
                                                         (let uu____6483 =
                                                            let uu____6490 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6490 b_t in
                                                          bind uu____6483
                                                            (fun uu____6521
                                                               ->
                                                               match uu____6521
                                                               with
                                                               | (t1, u) ->
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
                                              ([], [], []) bs in
                                          bind uu____6146
                                            (fun uu____6707 ->
                                               match uu____6707 with
                                               | (uvs, implicits, subst1) ->
                                                   let implicits1 =
                                                     FStar_List.rev implicits in
                                                   let uvs1 =
                                                     FStar_List.rev uvs in
                                                   let pre1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 pre in
                                                   let post1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 post in
                                                   let uu____6795 =
                                                     let uu____6799 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal in
                                                     let uu____6800 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1 in
                                                     let uu____6801 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal in
                                                     do_unify uu____6799
                                                       uu____6800 uu____6801 in
                                                   bind uu____6795
                                                     (fun b ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6812 =
                                                            let uu____6814 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal in
                                                            tts uu____6814
                                                              tm1 in
                                                          let uu____6815 =
                                                            let uu____6817 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal in
                                                            let uu____6818 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1 in
                                                            tts uu____6817
                                                              uu____6818 in
                                                          let uu____6819 =
                                                            let uu____6821 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal in
                                                            let uu____6822 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal in
                                                            tts uu____6821
                                                              uu____6822 in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6812
                                                            uu____6815
                                                            uu____6819
                                                        else
                                                          (let uu____6826 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit in
                                                           bind uu____6826
                                                             (fun uu____6834
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____6860
                                                                    =
                                                                    let uu____6863
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____6863 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6860 in
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                let appears
                                                                  uv goals =
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun g' ->
                                                                    let uu____6899
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6899)
                                                                    goals in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____6916
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                  match uu____6916
                                                                  with
                                                                  | (hd1,
                                                                    uu____6935)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____6962)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6979
                                                                    -> false) in
                                                                let uu____6981
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp
                                                                    ->
                                                                    let t1 =
                                                                    FStar_Util.now
                                                                    () in
                                                                    let uu____7024
                                                                    = imp in
                                                                    match uu____7024
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____7035
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____7035
                                                                    with
                                                                    | 
                                                                    (hd1,
                                                                    uu____7057)
                                                                    ->
                                                                    let uu____7082
                                                                    =
                                                                    let uu____7083
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____7083.FStar_Syntax_Syntax.n in
                                                                    (match uu____7082
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____7091)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___985_7111
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___985_7111.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___985_7111.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___985_7111.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___985_7111.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7114
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7120
                                                                    ->
                                                                    let uu____7121
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____7123
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7121
                                                                    uu____7123)
                                                                    (fun
                                                                    uu____7130
                                                                    ->
                                                                    let env =
                                                                    let uu___990_7132
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___990_7132.FStar_TypeChecker_Env.nbe)
                                                                    } in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                                    let uu____7135
                                                                    =
                                                                    let uu____7138
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7142
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar in
                                                                    let uu____7144
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7142
                                                                    uu____7144
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    let uu____7150
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    proc_guard
                                                                    uu____7138
                                                                    uu____7150
                                                                    g_typ in
                                                                    bind
                                                                    uu____7135
                                                                    (fun
                                                                    uu____7154
                                                                    -> ret [])))))) in
                                                                bind
                                                                  uu____6981
                                                                  (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____7218
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____7218
                                                                    then
                                                                    let uu____7223
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____7223
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____7238
                                                                    =
                                                                    let uu____7240
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____7240
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____7238)
                                                                    sub_goals1 in
                                                                    let uu____7241
                                                                    =
                                                                    let uu____7244
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7244
                                                                    guard in
                                                                    bind
                                                                    uu____7241
                                                                    (fun
                                                                    uu____7248
                                                                    ->
                                                                    let uu____7249
                                                                    =
                                                                    let uu____7252
                                                                    =
                                                                    let uu____7254
                                                                    =
                                                                    let uu____7256
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    let uu____7257
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1 in
                                                                    istrivial
                                                                    uu____7256
                                                                    uu____7257 in
                                                                    Prims.op_Negation
                                                                    uu____7254 in
                                                                    if
                                                                    uu____7252
                                                                    then
                                                                    let uu____7261
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7261
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret () in
                                                                    bind
                                                                    uu____7249
                                                                    (fun
                                                                    uu____7266
                                                                    ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))) in
      focus uu____6020 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6017
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____7290 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____7290 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____7300::(e1, uu____7302)::(e2, uu____7304)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____7365 ->
        let uu____7368 = FStar_Syntax_Util.unb2t typ in
        (match uu____7368 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____7383 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print1 "GG t = %s\n" uu____7383);
              (let uu____7386 = FStar_Syntax_Util.head_and_args t in
               match uu____7386 with
               | (hd1, args) ->
                   let uu____7435 =
                     let uu____7450 =
                       let uu____7451 = FStar_Syntax_Subst.compress hd1 in
                       uu____7451.FStar_Syntax_Syntax.n in
                     (uu____7450, args) in
                   (match uu____7435 with
                    | (FStar_Syntax_Syntax.Tm_fvar fv,
                       (uu____7471, FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____7472))::(e1,
                                                                    FStar_Pervasives_Native.None)::
                       (e2, FStar_Pervasives_Native.None)::[]) when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____7537 =
                            FStar_Syntax_Print.term_to_string e1 in
                          let uu____7539 =
                            FStar_Syntax_Print.term_to_string e2 in
                          FStar_Util.print2 "wat %s -- %s\n" uu____7537
                            uu____7539);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____7546 -> FStar_Pervasives_Native.None))))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____7583 = destruct_eq' typ in
    match uu____7583 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____7613 = FStar_Syntax_Util.un_squash typ in
        (match uu____7613 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu____7682 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____7682 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7740 = aux e' in
               FStar_Util.map_opt uu____7740
                 (fun uu____7771 ->
                    match uu____7771 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____7797 = aux e in
      FStar_Util.map_opt uu____7797
        (fun uu____7828 ->
           match uu____7828 with
           | (e', bv, bvs) -> (e', bv, (FStar_List.rev bvs)))
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e ->
    fun bvs ->
      FStar_List.fold_left
        (fun e1 -> fun b -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option)
  =
  fun b1 ->
    fun b2 ->
      fun s ->
        fun g ->
          let uu____7902 =
            let uu____7913 = FStar_Tactics_Types.goal_env g in
            split_env b1 uu____7913 in
          FStar_Util.map_opt uu____7902
            (fun uu____7931 ->
               match uu____7931 with
               | (e0, b11, bvs) ->
                   let s1 bv =
                     let uu___1087_7953 = bv in
                     let uu____7954 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1087_7953.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1087_7953.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7954
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let new_env = push_bvs e0 (b2 :: bvs1) in
                   let new_goal =
                     let uu___1091_7962 = g.FStar_Tactics_Types.goal_ctx_uvar in
                     let uu____7963 =
                       FStar_TypeChecker_Env.all_binders new_env in
                     let uu____7972 =
                       let uu____7975 = FStar_Tactics_Types.goal_type g in
                       FStar_Syntax_Subst.subst s uu____7975 in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1091_7962.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7963;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7972;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1091_7962.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1091_7962.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1091_7962.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1091_7962.FStar_Syntax_Syntax.ctx_uvar_meta)
                     } in
                   let uu___1094_7976 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1094_7976.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1094_7976.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1094_7976.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1094_7976.FStar_Tactics_Types.label)
                   })
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h ->
    let uu____7987 =
      let uu____7990 = cur_goal () in
      bind uu____7990
        (fun goal ->
           let uu____7998 = h in
           match uu____7998 with
           | (bv, uu____8002) ->
               mlog
                 (fun uu____8010 ->
                    let uu____8011 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____8013 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8011
                      uu____8013)
                 (fun uu____8018 ->
                    let uu____8019 =
                      let uu____8030 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____8030 in
                    match uu____8019 with
                    | FStar_Pervasives_Native.None ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____8057 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort in
                        (match uu____8057 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____8072 =
                               let uu____8073 = FStar_Syntax_Subst.compress x in
                               uu____8073.FStar_Syntax_Syntax.n in
                             (match uu____8072 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let s1 bv2 =
                                    let uu___1117_8090 = bv2 in
                                    let uu____8091 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1117_8090.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1117_8090.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8091
                                    } in
                                  let bvs1 = FStar_List.map s1 bvs in
                                  let new_env = push_bvs e0 (bv1 :: bvs1) in
                                  let new_goal =
                                    let uu___1121_8099 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar in
                                    let uu____8100 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env in
                                    let uu____8109 =
                                      let uu____8112 =
                                        FStar_Tactics_Types.goal_type goal in
                                      FStar_Syntax_Subst.subst s uu____8112 in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1121_8099.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8100;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8109;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1121_8099.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1121_8099.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1121_8099.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1121_8099.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    } in
                                  replace_cur
                                    (let uu___1124_8115 = goal in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1124_8115.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1124_8115.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1124_8115.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1124_8115.FStar_Tactics_Types.label)
                                     })
                              | uu____8116 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8118 -> fail "Not an equality hypothesis"))) in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7987
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b ->
    fun s ->
      let uu____8148 =
        let uu____8151 = cur_goal () in
        bind uu____8151
          (fun goal ->
             let uu____8162 = b in
             match uu____8162 with
             | (bv, uu____8166) ->
                 let bv' =
                   let uu____8172 =
                     let uu___1135_8173 = bv in
                     let uu____8174 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)) in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8174;
                       FStar_Syntax_Syntax.index =
                         (uu___1135_8173.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1135_8173.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____8172 in
                 let s1 =
                   let uu____8179 =
                     let uu____8180 =
                       let uu____8187 = FStar_Syntax_Syntax.bv_to_name bv' in
                       (bv, uu____8187) in
                     FStar_Syntax_Syntax.NT uu____8180 in
                   [uu____8179] in
                 let uu____8192 = subst_goal bv bv' s1 goal in
                 (match uu____8192 with
                  | FStar_Pervasives_Native.None ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1)) in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8148
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b ->
    let uu____8214 =
      let uu____8217 = cur_goal () in
      bind uu____8217
        (fun goal ->
           let uu____8226 = b in
           match uu____8226 with
           | (bv, uu____8230) ->
               let uu____8235 =
                 let uu____8246 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____8246 in
               (match uu____8235 with
                | FStar_Pervasives_Native.None ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____8273 = FStar_Syntax_Util.type_u () in
                    (match uu____8273 with
                     | (ty, u) ->
                         let uu____8282 = new_uvar "binder_retype" e0 ty in
                         bind uu____8282
                           (fun uu____8301 ->
                              match uu____8301 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___1159_8311 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1159_8311.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1159_8311.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____8315 =
                                      let uu____8316 =
                                        let uu____8323 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____8323) in
                                      FStar_Syntax_Syntax.NT uu____8316 in
                                    [uu____8315] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___1164_8335 = b1 in
                                         let uu____8336 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1164_8335.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1164_8335.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8336
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  bind __dismiss
                                    (fun uu____8343 ->
                                       let new_goal =
                                         let uu____8345 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____8346 =
                                           let uu____8347 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____8347 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8345 uu____8346 in
                                       let uu____8348 = add_goals [new_goal] in
                                       bind uu____8348
                                         (fun uu____8353 ->
                                            let uu____8354 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8354
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label)))))) in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8214
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s ->
    fun b ->
      let uu____8380 =
        let uu____8383 = cur_goal () in
        bind uu____8383
          (fun goal ->
             let uu____8392 = b in
             match uu____8392 with
             | (bv, uu____8396) ->
                 let uu____8401 =
                   let uu____8412 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____8412 in
                 (match uu____8401 with
                  | FStar_Pervasives_Native.None ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____8442 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8442 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___1185_8447 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1185_8447.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1185_8447.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____8449 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      replace_cur uu____8449)) in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8380
let (revert : unit -> unit tac) =
  fun uu____8462 ->
    let uu____8465 = cur_goal () in
    bind uu____8465
      (fun goal ->
         let uu____8471 =
           let uu____8478 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____8478 in
         match uu____8471 with
         | FStar_Pervasives_Native.None ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____8495 =
                 let uu____8498 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____8498 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8495 in
             let uu____8513 = new_uvar "revert" env' typ' in
             bind uu____8513
               (fun uu____8529 ->
                  match uu____8529 with
                  | (r, u_r) ->
                      let uu____8538 =
                        let uu____8541 =
                          let uu____8542 =
                            let uu____8543 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____8543.FStar_Syntax_Syntax.pos in
                          let uu____8546 =
                            let uu____8551 =
                              let uu____8552 =
                                let uu____8561 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____8561 in
                              [uu____8552] in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8551 in
                          uu____8546 FStar_Pervasives_Native.None uu____8542 in
                        set_solution goal uu____8541 in
                      bind uu____8538
                        (fun uu____8580 ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label in
                           replace_cur g)))
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____8594 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____8594
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    let uu____8610 = cur_goal () in
    bind uu____8610
      (fun goal ->
         mlog
           (fun uu____8618 ->
              let uu____8619 = FStar_Syntax_Print.binder_to_string b in
              let uu____8621 =
                let uu____8623 =
                  let uu____8625 =
                    let uu____8634 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____8634 in
                  FStar_All.pipe_right uu____8625 FStar_List.length in
                FStar_All.pipe_right uu____8623 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8619 uu____8621)
           (fun uu____8655 ->
              let uu____8656 =
                let uu____8667 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____8667 in
              match uu____8656 with
              | FStar_Pervasives_Native.None ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8712 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____8712
                        then
                          let uu____8717 =
                            let uu____8719 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8719 in
                          fail uu____8717
                        else check1 bvs2 in
                  let uu____8724 =
                    let uu____8726 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____8726 in
                  if uu____8724
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8733 = check1 bvs in
                     bind uu____8733
                       (fun uu____8739 ->
                          let env' = push_bvs e' bvs in
                          let uu____8741 =
                            let uu____8748 =
                              FStar_Tactics_Types.goal_type goal in
                            new_uvar "clear.witness" env' uu____8748 in
                          bind uu____8741
                            (fun uu____8758 ->
                               match uu____8758 with
                               | (ut, uvar_ut) ->
                                   let uu____8767 = set_solution goal ut in
                                   bind uu____8767
                                     (fun uu____8772 ->
                                        let uu____8773 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        replace_cur uu____8773))))))
let (clear_top : unit -> unit tac) =
  fun uu____8781 ->
    let uu____8784 = cur_goal () in
    bind uu____8784
      (fun goal ->
         let uu____8790 =
           let uu____8797 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____8797 in
         match uu____8790 with
         | FStar_Pervasives_Native.None -> fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____8806) ->
             let uu____8811 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____8811)
let (prune : Prims.string -> unit tac) =
  fun s ->
    let uu____8824 = cur_goal () in
    bind uu____8824
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____8834 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8834 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         bind __dismiss (fun uu____8837 -> add_goals [g']))
let (addns : Prims.string -> unit tac) =
  fun s ->
    let uu____8850 = cur_goal () in
    bind uu____8850
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____8860 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8860 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         bind __dismiss (fun uu____8863 -> add_goals [g']))
let rec (tac_fold_env :
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun d ->
    fun f ->
      fun env ->
        fun t ->
          let tn =
            let uu____8904 = FStar_Syntax_Subst.compress t in
            uu____8904.FStar_Syntax_Syntax.n in
          let uu____8907 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1369_8914 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1369_8914.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1369_8914.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____8907
            (fun t1 ->
               let ff = tac_fold_env d f env in
               let tn1 =
                 let uu____8931 =
                   let uu____8932 = FStar_Syntax_Subst.compress t1 in
                   uu____8932.FStar_Syntax_Syntax.n in
                 match uu____8931 with
                 | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
                     let uu____8963 = ff hd1 in
                     bind uu____8963
                       (fun hd2 ->
                          let fa uu____8989 =
                            match uu____8989 with
                            | (a, q) ->
                                let uu____9010 = ff a in
                                bind uu____9010 (fun a1 -> ret (a1, q)) in
                          let uu____9029 = mapM fa args in
                          bind uu____9029
                            (fun args1 ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs, t2, k) ->
                     let uu____9111 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____9111 with
                      | (bs1, t') ->
                          let uu____9120 =
                            let uu____9123 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____9123 t' in
                          bind uu____9120
                            (fun t'' ->
                               let uu____9127 =
                                 let uu____9128 =
                                   let uu____9147 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____9156 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____9147, uu____9156, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____9128 in
                               ret uu____9127))
                 | FStar_Syntax_Syntax.Tm_arrow (bs, k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1, brs) ->
                     let uu____9231 = ff hd1 in
                     bind uu____9231
                       (fun hd2 ->
                          let ffb br =
                            let uu____9246 =
                              FStar_Syntax_Subst.open_branch br in
                            match uu____9246 with
                            | (pat, w, e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat in
                                let ff1 =
                                  let uu____9278 =
                                    FStar_TypeChecker_Env.push_bvs env bvs in
                                  tac_fold_env d f uu____9278 in
                                let uu____9279 = ff1 e in
                                bind uu____9279
                                  (fun e1 ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1) in
                                     ret br1) in
                          let uu____9294 = mapM ffb brs in
                          bind uu____9294
                            (fun brs1 ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false,
                       { FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                         FStar_Syntax_Syntax.lbunivs = uu____9338;
                         FStar_Syntax_Syntax.lbtyp = uu____9339;
                         FStar_Syntax_Syntax.lbeff = uu____9340;
                         FStar_Syntax_Syntax.lbdef = def;
                         FStar_Syntax_Syntax.lbattrs = uu____9342;
                         FStar_Syntax_Syntax.lbpos = uu____9343;_}::[]),
                      e)
                     ->
                     let lb =
                       let uu____9371 =
                         let uu____9372 = FStar_Syntax_Subst.compress t1 in
                         uu____9372.FStar_Syntax_Syntax.n in
                       match uu____9371 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false, lb::[]), uu____9376) -> lb
                       | uu____9392 -> failwith "impossible" in
                     let fflb lb1 =
                       let uu____9402 = ff lb1.FStar_Syntax_Syntax.lbdef in
                       bind uu____9402
                         (fun def1 ->
                            ret
                              (let uu___1322_9408 = lb1 in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1322_9408.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1322_9408.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1322_9408.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1322_9408.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1322_9408.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1322_9408.FStar_Syntax_Syntax.lbpos)
                               })) in
                     let uu____9409 = fflb lb in
                     bind uu____9409
                       (fun lb1 ->
                          let uu____9419 =
                            let uu____9424 =
                              let uu____9425 =
                                FStar_Syntax_Syntax.mk_binder bv in
                              [uu____9425] in
                            FStar_Syntax_Subst.open_term uu____9424 e in
                          match uu____9419 with
                          | (bs, e1) ->
                              let ff1 =
                                let uu____9455 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                tac_fold_env d f uu____9455 in
                              let uu____9456 = ff1 e1 in
                              bind uu____9456
                                (fun e2 ->
                                   let e3 = FStar_Syntax_Subst.close bs e2 in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true, lbs), e) ->
                     let fflb lb =
                       let uu____9503 = ff lb.FStar_Syntax_Syntax.lbdef in
                       bind uu____9503
                         (fun def ->
                            ret
                              (let uu___1340_9509 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1340_9509.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1340_9509.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1340_9509.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1340_9509.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1340_9509.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1340_9509.FStar_Syntax_Syntax.lbpos)
                               })) in
                     let uu____9510 = FStar_Syntax_Subst.open_let_rec lbs e in
                     (match uu____9510 with
                      | (lbs1, e1) ->
                          let uu____9525 = mapM fflb lbs1 in
                          bind uu____9525
                            (fun lbs2 ->
                               let uu____9537 = ff e1 in
                               bind uu____9537
                                 (fun e2 ->
                                    let uu____9545 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2 in
                                    match uu____9545 with
                                    | (lbs3, e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2, asc, eff) ->
                     let uu____9616 = ff t2 in
                     bind uu____9616
                       (fun t3 ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2, m) ->
                     let uu____9647 = ff t2 in
                     bind uu____9647
                       (fun t3 -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9654 -> ret tn in
               bind tn1
                 (fun tn2 ->
                    let t' =
                      let uu___1364_9661 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1364_9661.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1364_9661.FStar_Syntax_Syntax.vars)
                      } in
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
  fun ps ->
    fun tau ->
      fun opts ->
        fun label1 ->
          fun env ->
            fun t ->
              let uu____9708 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1377_9717 = env in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1377_9717.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1377_9717.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1377_9717.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1377_9717.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1377_9717.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1377_9717.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1377_9717.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1377_9717.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1377_9717.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1377_9717.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1377_9717.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1377_9717.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1377_9717.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1377_9717.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1377_9717.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1377_9717.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1377_9717.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1377_9717.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1377_9717.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1377_9717.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1377_9717.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1377_9717.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1377_9717.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1377_9717.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1377_9717.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1377_9717.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1377_9717.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1377_9717.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1377_9717.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1377_9717.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1377_9717.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1377_9717.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1377_9717.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1377_9717.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1377_9717.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1377_9717.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1377_9717.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1377_9717.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1377_9717.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1377_9717.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1377_9717.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1377_9717.FStar_TypeChecker_Env.nbe)
                   }) t in
              match uu____9708 with
              | (t1, lcomp, g) ->
                  let uu____9724 =
                    (let uu____9728 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                     Prims.op_Negation uu____9728) ||
                      (let uu____9731 = FStar_TypeChecker_Env.is_trivial g in
                       Prims.op_Negation uu____9731) in
                  if uu____9724
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                       let uu____9742 = new_uvar "pointwise_rec" env typ in
                       bind uu____9742
                         (fun uu____9759 ->
                            match uu____9759 with
                            | (ut, uvar_ut) ->
                                (log ps
                                   (fun uu____9772 ->
                                      let uu____9773 =
                                        FStar_Syntax_Print.term_to_string t1 in
                                      let uu____9775 =
                                        FStar_Syntax_Print.term_to_string ut in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9773 uu____9775);
                                 (let uu____9778 =
                                    let uu____9781 =
                                      let uu____9782 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ in
                                      FStar_Syntax_Util.mk_eq2 uu____9782 typ
                                        t1 ut in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9781
                                      opts label1 in
                                  bind uu____9778
                                    (fun uu____9786 ->
                                       let uu____9787 =
                                         bind tau
                                           (fun uu____9793 ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut in
                                              log ps
                                                (fun uu____9799 ->
                                                   let uu____9800 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   let uu____9802 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1 in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9800 uu____9802);
                                              ret ut1) in
                                       focus uu____9787)))) in
                     let uu____9805 = catch rewrite_eq in
                     bind uu____9805
                       (fun x ->
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
  fun f ->
    fun env ->
      fun ctrl ->
        fun t ->
          let keep_going c =
            if c = proceedToNextSubtree then keepGoing else c in
          let maybe_continue ctrl1 t1 k =
            if ctrl1 = globalStop
            then ret (t1, globalStop)
            else
              if ctrl1 = proceedToNextSubtree
              then ret (t1, keepGoing)
              else k t1 in
          let uu____10017 = FStar_Syntax_Subst.compress t in
          maybe_continue ctrl uu____10017
            (fun t1 ->
               let uu____10025 =
                 f env
                   (let uu___1454_10033 = t1 in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1454_10033.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1454_10033.FStar_Syntax_Syntax.vars)
                    }) in
               bind uu____10025
                 (fun uu____10049 ->
                    match uu____10049 with
                    | (t2, ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3 ->
                             let uu____10072 =
                               let uu____10073 =
                                 FStar_Syntax_Subst.compress t3 in
                               uu____10073.FStar_Syntax_Syntax.n in
                             match uu____10072 with
                             | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
                                 let uu____10110 =
                                   ctrl_tac_fold f env ctrl1 hd1 in
                                 bind uu____10110
                                   (fun uu____10132 ->
                                      match uu____10132 with
                                      | (hd2, ctrl2) ->
                                          let ctrl3 = keep_going ctrl2 in
                                          let uu____10148 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args in
                                          bind uu____10148
                                            (fun uu____10172 ->
                                               match uu____10172 with
                                               | (args1, ctrl4) ->
                                                   ret
                                                     ((let uu___1434_10202 =
                                                         t3 in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1434_10202.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1434_10202.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
                                 let uu____10244 =
                                   FStar_Syntax_Subst.open_term bs t4 in
                                 (match uu____10244 with
                                  | (bs1, t') ->
                                      let uu____10259 =
                                        let uu____10266 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1 in
                                        ctrl_tac_fold f uu____10266 ctrl1 t' in
                                      bind uu____10259
                                        (fun uu____10281 ->
                                           match uu____10281 with
                                           | (t'', ctrl2) ->
                                               let uu____10296 =
                                                 let uu____10303 =
                                                   let uu___1447_10306 = t4 in
                                                   let uu____10309 =
                                                     let uu____10310 =
                                                       let uu____10329 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1 in
                                                       let uu____10338 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t'' in
                                                       (uu____10329,
                                                         uu____10338, k) in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10310 in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10309;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1447_10306.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1447_10306.FStar_Syntax_Syntax.vars)
                                                   } in
                                                 (uu____10303, ctrl2) in
                                               ret uu____10296))
                             | FStar_Syntax_Syntax.Tm_arrow (bs, k) ->
                                 ret (t3, ctrl1)
                             | uu____10391 -> ret (t3, ctrl1))))
and (ctrl_tac_fold_args :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl ->
        FStar_Syntax_Syntax.arg Prims.list ->
          FStar_Syntax_Syntax.arg Prims.list ctrl_tac)
  =
  fun f ->
    fun env ->
      fun ctrl ->
        fun ts ->
          match ts with
          | [] -> ret ([], ctrl)
          | (t, q)::ts1 ->
              let uu____10437 = ctrl_tac_fold f env ctrl t in
              bind uu____10437
                (fun uu____10458 ->
                   match uu____10458 with
                   | (t1, ctrl1) ->
                       let uu____10473 = ctrl_tac_fold_args f env ctrl1 ts1 in
                       bind uu____10473
                         (fun uu____10497 ->
                            match uu____10497 with
                            | (ts2, ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))
let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          Prims.string ->
            FStar_TypeChecker_Env.env ->
              FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps ->
    fun ctrl ->
      fun rewriter ->
        fun opts ->
          fun label1 ->
            fun env ->
              fun t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let uu____10588 =
                  let uu____10596 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1 in
                  bind uu____10596
                    (fun uu____10607 ->
                       let uu____10608 = ctrl t1 in
                       bind uu____10608
                         (fun res ->
                            let uu____10634 = trivial () in
                            bind uu____10634 (fun uu____10643 -> ret res))) in
                bind uu____10588
                  (fun uu____10661 ->
                     match uu____10661 with
                     | (should_rewrite, ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10690 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1484_10699 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1484_10699.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1484_10699.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1484_10699.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1484_10699.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1484_10699.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1484_10699.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1484_10699.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1484_10699.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1484_10699.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1484_10699.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1484_10699.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1484_10699.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1484_10699.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1484_10699.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1484_10699.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1484_10699.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1484_10699.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1484_10699.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1484_10699.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1484_10699.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1484_10699.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1484_10699.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1484_10699.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1484_10699.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1484_10699.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1484_10699.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1484_10699.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1484_10699.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1484_10699.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1484_10699.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1484_10699.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1484_10699.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1484_10699.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1484_10699.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1484_10699.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1484_10699.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1484_10699.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1484_10699.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1484_10699.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1484_10699.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1484_10699.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1484_10699.FStar_TypeChecker_Env.nbe)
                                 }) t1 in
                            match uu____10690 with
                            | (t2, lcomp, g) ->
                                let uu____10710 =
                                  (let uu____10714 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp in
                                   Prims.op_Negation uu____10714) ||
                                    (let uu____10717 =
                                       FStar_TypeChecker_Env.is_trivial g in
                                     Prims.op_Negation uu____10717) in
                                if uu____10710
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ in
                                   let uu____10733 =
                                     new_uvar "pointwise_rec" env typ in
                                   bind uu____10733
                                     (fun uu____10754 ->
                                        match uu____10754 with
                                        | (ut, uvar_ut) ->
                                            (log ps
                                               (fun uu____10771 ->
                                                  let uu____10772 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2 in
                                                  let uu____10774 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10772 uu____10774);
                                             (let uu____10777 =
                                                let uu____10780 =
                                                  let uu____10781 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10781 typ t2 ut in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10780 opts label1 in
                                              bind uu____10777
                                                (fun uu____10789 ->
                                                   let uu____10790 =
                                                     bind rewriter
                                                       (fun uu____10804 ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut in
                                                          log ps
                                                            (fun uu____10810
                                                               ->
                                                               let uu____10811
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2 in
                                                               let uu____10813
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1 in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10811
                                                                 uu____10813);
                                                          ret (ut1, ctrl1)) in
                                                   focus uu____10790)))))))
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl ->
    fun rewriter ->
      let uu____10858 =
        bind get
          (fun ps ->
             let uu____10868 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals" in
             match uu____10868 with
             | (g, gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g in
                 (log ps
                    (fun uu____10906 ->
                       let uu____10907 =
                         FStar_Syntax_Print.term_to_string gt1 in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10907);
                  bind dismiss_all
                    (fun uu____10912 ->
                       let uu____10913 =
                         let uu____10920 = FStar_Tactics_Types.goal_env g in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10920
                           keepGoing gt1 in
                       bind uu____10913
                         (fun uu____10930 ->
                            match uu____10930 with
                            | (gt', uu____10938) ->
                                (log ps
                                   (fun uu____10942 ->
                                      let uu____10943 =
                                        FStar_Syntax_Print.term_to_string gt' in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10943);
                                 (let uu____10946 = push_goals gs in
                                  bind uu____10946
                                    (fun uu____10951 ->
                                       let uu____10952 =
                                         let uu____10955 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt' in
                                         [uu____10955] in
                                       add_goals uu____10952))))))) in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10858
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d ->
    fun tau ->
      let uu____10980 =
        bind get
          (fun ps ->
             let uu____10990 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals" in
             match uu____10990 with
             | (g, gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g in
                 (log ps
                    (fun uu____11028 ->
                       let uu____11029 =
                         FStar_Syntax_Print.term_to_string gt1 in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11029);
                  bind dismiss_all
                    (fun uu____11034 ->
                       let uu____11035 =
                         let uu____11038 = FStar_Tactics_Types.goal_env g in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11038 gt1 in
                       bind uu____11035
                         (fun gt' ->
                            log ps
                              (fun uu____11046 ->
                                 let uu____11047 =
                                   FStar_Syntax_Print.term_to_string gt' in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11047);
                            (let uu____11050 = push_goals gs in
                             bind uu____11050
                               (fun uu____11055 ->
                                  let uu____11056 =
                                    let uu____11059 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt' in
                                    [uu____11059] in
                                  add_goals uu____11056)))))) in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10980
let (trefl : unit -> unit tac) =
  fun uu____11072 ->
    let uu____11075 =
      let uu____11078 = cur_goal () in
      bind uu____11078
        (fun g ->
           let uu____11096 =
             let uu____11101 = FStar_Tactics_Types.goal_type g in
             FStar_Syntax_Util.un_squash uu____11101 in
           match uu____11096 with
           | FStar_Pervasives_Native.Some t ->
               let uu____11109 = FStar_Syntax_Util.head_and_args' t in
               (match uu____11109 with
                | (hd1, args) ->
                    let uu____11148 =
                      let uu____11161 =
                        let uu____11162 = FStar_Syntax_Util.un_uinst hd1 in
                        uu____11162.FStar_Syntax_Syntax.n in
                      (uu____11161, args) in
                    (match uu____11148 with
                     | (FStar_Syntax_Syntax.Tm_fvar fv,
                        uu____11176::(l, uu____11178)::(r, uu____11180)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____11227 =
                           let uu____11231 = FStar_Tactics_Types.goal_env g in
                           do_unify uu____11231 l r in
                         bind uu____11227
                           (fun b ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____11242 =
                                     FStar_Tactics_Types.goal_env g in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11242 l in
                                 let r1 =
                                   let uu____11244 =
                                     FStar_Tactics_Types.goal_env g in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____11244 r in
                                 let uu____11245 =
                                   let uu____11249 =
                                     FStar_Tactics_Types.goal_env g in
                                   do_unify uu____11249 l1 r1 in
                                 bind uu____11245
                                   (fun b1 ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____11259 =
                                           let uu____11261 =
                                             FStar_Tactics_Types.goal_env g in
                                           tts uu____11261 l1 in
                                         let uu____11262 =
                                           let uu____11264 =
                                             FStar_Tactics_Types.goal_env g in
                                           tts uu____11264 r1 in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____11259 uu____11262))))
                     | (hd2, uu____11267) ->
                         let uu____11284 =
                           let uu____11286 = FStar_Tactics_Types.goal_env g in
                           tts uu____11286 t in
                         fail1 "trefl: not an equality (%s)" uu____11284))
           | FStar_Pervasives_Native.None -> fail "not an irrelevant goal") in
    FStar_All.pipe_left (wrap_err "trefl") uu____11075
let (dup : unit -> unit tac) =
  fun uu____11303 ->
    let uu____11306 = cur_goal () in
    bind uu____11306
      (fun g ->
         let uu____11312 =
           let uu____11319 = FStar_Tactics_Types.goal_env g in
           let uu____11320 = FStar_Tactics_Types.goal_type g in
           new_uvar "dup" uu____11319 uu____11320 in
         bind uu____11312
           (fun uu____11330 ->
              match uu____11330 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1576_11340 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1576_11340.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1576_11340.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1576_11340.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1576_11340.FStar_Tactics_Types.label)
                    } in
                  bind __dismiss
                    (fun uu____11343 ->
                       let uu____11344 =
                         let uu____11347 = FStar_Tactics_Types.goal_env g in
                         let uu____11348 =
                           let uu____11349 =
                             let uu____11350 = FStar_Tactics_Types.goal_env g in
                             let uu____11351 =
                               FStar_Tactics_Types.goal_type g in
                             FStar_TypeChecker_TcTerm.universe_of uu____11350
                               uu____11351 in
                           let uu____11352 = FStar_Tactics_Types.goal_type g in
                           let uu____11353 =
                             FStar_Tactics_Types.goal_witness g in
                           FStar_Syntax_Util.mk_eq2 uu____11349 uu____11352 u
                             uu____11353 in
                         add_irrelevant_goal "dup equation" uu____11347
                           uu____11348 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label in
                       bind uu____11344
                         (fun uu____11357 ->
                            let uu____11358 = add_goals [g'] in
                            bind uu____11358 (fun uu____11362 -> ret ())))))
let rec longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs, y::ys) ->
              let uu____11488 = f x y in
              if uu____11488 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11511 -> (acc, l11, l21) in
        let uu____11526 = aux [] l1 l2 in
        match uu____11526 with
        | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs1 bs f =
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f in
      let uu____11632 = get_phi g1 in
      match uu____11632 with
      | FStar_Pervasives_Native.None -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11639 = get_phi g2 in
          (match uu____11639 with
           | FStar_Pervasives_Native.None -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____11652 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____11652 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____11683 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs1 uu____11683 phi1 in
                    let t2 =
                      let uu____11693 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs1 uu____11693 phi2 in
                    let uu____11702 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    bind uu____11702
                      (fun uu____11707 ->
                         let uu____11708 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         bind uu____11708
                           (fun uu____11715 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1627_11720 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____11721 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100") in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1627_11720.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1627_11720.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1627_11720.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1627_11720.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11721;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1627_11720.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1627_11720.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1627_11720.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1627_11720.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1627_11720.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1627_11720.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1627_11720.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1627_11720.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1627_11720.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1627_11720.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1627_11720.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1627_11720.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1627_11720.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1627_11720.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1627_11720.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1627_11720.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1627_11720.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1627_11720.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1627_11720.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1627_11720.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1627_11720.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1627_11720.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1627_11720.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1627_11720.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1627_11720.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1627_11720.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1627_11720.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1627_11720.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1627_11720.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1627_11720.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1627_11720.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1627_11720.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1627_11720.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1627_11720.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1627_11720.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1627_11720.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1627_11720.FStar_TypeChecker_Env.nbe)
                                } in
                              let uu____11725 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              bind uu____11725
                                (fun goal ->
                                   mlog
                                     (fun uu____11735 ->
                                        let uu____11736 =
                                          goal_to_string_verbose g1 in
                                        let uu____11738 =
                                          goal_to_string_verbose g2 in
                                        let uu____11740 =
                                          goal_to_string_verbose goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11736 uu____11738 uu____11740)
                                     (fun uu____11744 -> ret goal))))))
let (join : unit -> unit tac) =
  fun uu____11752 ->
    bind get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11768 =
               set
                 (let uu___1642_11773 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1642_11773.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1642_11773.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1642_11773.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1642_11773.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1642_11773.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1642_11773.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1642_11773.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1642_11773.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1642_11773.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1642_11773.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1642_11773.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1642_11773.FStar_Tactics_Types.local_state)
                  }) in
             bind uu____11768
               (fun uu____11776 ->
                  let uu____11777 = join_goals g1 g2 in
                  bind uu____11777 (fun g12 -> add_goals [g12]))
         | uu____11782 -> fail "join: less than 2 goals")
let (set_options : Prims.string -> unit tac) =
  fun s ->
    let uu____11798 =
      let uu____11801 = cur_goal () in
      bind uu____11801
        (fun g ->
           FStar_Options.push ();
           (let uu____11814 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____11814);
           (let res = FStar_Options.set_options FStar_Options.Set s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1653_11821 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1653_11821.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1653_11821.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1653_11821.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1653_11821.FStar_Tactics_Types.label)
                   } in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (wrap_err "set_options") uu____11798
let (top_env : unit -> env tac) =
  fun uu____11838 ->
    bind get
      (fun ps -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11853 ->
    let uu____11857 = cur_goal () in
    bind uu____11857
      (fun g ->
         let uu____11864 =
           (FStar_Options.lax ()) ||
             (let uu____11867 = FStar_Tactics_Types.goal_env g in
              uu____11867.FStar_TypeChecker_Env.lax) in
         ret uu____11864)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty ->
    fun tm ->
      let uu____11884 =
        mlog
          (fun uu____11889 ->
             let uu____11890 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11890)
          (fun uu____11895 ->
             let uu____11896 = cur_goal () in
             bind uu____11896
               (fun goal ->
                  let env =
                    let uu____11904 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____11904 ty in
                  let uu____11905 = __tc_ghost env tm in
                  bind uu____11905
                    (fun uu____11924 ->
                       match uu____11924 with
                       | (tm1, typ, guard) ->
                           mlog
                             (fun uu____11938 ->
                                let uu____11939 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11939)
                             (fun uu____11943 ->
                                mlog
                                  (fun uu____11946 ->
                                     let uu____11947 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11947)
                                  (fun uu____11952 ->
                                     let uu____11953 =
                                       proc_guard "unquote" env guard in
                                     bind uu____11953
                                       (fun uu____11958 -> ret tm1)))))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____11884
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env ->
    fun ty ->
      let uu____11983 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____11989 =
              let uu____11996 =
                let uu____11997 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11997 in
              new_uvar "uvar_env.2" env uu____11996 in
            bind uu____11989
              (fun uu____12014 ->
                 match uu____12014 with | (typ, uvar_typ) -> ret typ) in
      bind uu____11983
        (fun typ ->
           let uu____12026 = new_uvar "uvar_env" env typ in
           bind uu____12026
             (fun uu____12041 ->
                match uu____12041 with | (t, uvar_t) -> ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t ->
    let uu____12060 =
      bind get
        (fun ps ->
           let env = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12079 -> g.FStar_Tactics_Types.opts
             | uu____12082 -> FStar_Options.peek () in
           let uu____12085 = FStar_Syntax_Util.head_and_args t in
           match uu____12085 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____12105);
                FStar_Syntax_Syntax.pos = uu____12106;
                FStar_Syntax_Syntax.vars = uu____12107;_},
              uu____12108) ->
               let env1 =
                 let uu___1707_12150 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1707_12150.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1707_12150.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1707_12150.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1707_12150.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1707_12150.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1707_12150.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1707_12150.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1707_12150.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1707_12150.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1707_12150.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1707_12150.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1707_12150.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1707_12150.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1707_12150.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1707_12150.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1707_12150.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1707_12150.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1707_12150.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1707_12150.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1707_12150.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1707_12150.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1707_12150.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1707_12150.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1707_12150.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1707_12150.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1707_12150.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1707_12150.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1707_12150.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1707_12150.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1707_12150.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1707_12150.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1707_12150.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1707_12150.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1707_12150.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1707_12150.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1707_12150.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1707_12150.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1707_12150.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1707_12150.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1707_12150.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1707_12150.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1707_12150.FStar_TypeChecker_Env.nbe)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false "" in
               let uu____12154 =
                 let uu____12157 = bnorm_goal g in [uu____12157] in
               add_goals uu____12154
           | uu____12158 -> fail "not a uvar") in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12060
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1 ->
    fun t2 ->
      let comp =
        bind t1
          (fun b ->
             let uu____12220 = if b then t2 else ret false in
             bind uu____12220 (fun b' -> if b' then ret b' else fail "")) in
      let uu____12246 = trytac comp in
      bind uu____12246
        (fun uu___4_12258 ->
           match uu___4_12258 with
           | FStar_Pervasives_Native.Some (true) -> ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> ret false)
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____12300 =
          bind get
            (fun ps ->
               let uu____12308 = __tc e t1 in
               bind uu____12308
                 (fun uu____12329 ->
                    match uu____12329 with
                    | (t11, ty1, g1) ->
                        let uu____12342 = __tc e t2 in
                        bind uu____12342
                          (fun uu____12363 ->
                             match uu____12363 with
                             | (t21, ty2, g2) ->
                                 let uu____12376 =
                                   proc_guard "unify_env g1" e g1 in
                                 bind uu____12376
                                   (fun uu____12383 ->
                                      let uu____12384 =
                                        proc_guard "unify_env g2" e g2 in
                                      bind uu____12384
                                        (fun uu____12392 ->
                                           let uu____12393 =
                                             do_unify e ty1 ty2 in
                                           let uu____12397 =
                                             do_unify e t11 t21 in
                                           tac_and uu____12393 uu____12397))))) in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12300
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        bind idtac
          (fun uu____12445 ->
             let uu____12446 = FStar_Options.unsafe_tactic_exec () in
             if uu____12446
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input) in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let (fresh_bv_named :
  Prims.string -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm ->
    fun t ->
      bind idtac
        (fun uu____12480 ->
           let uu____12481 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           ret uu____12481)
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty ->
    let uu____12492 =
      mlog
        (fun uu____12497 ->
           let uu____12498 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____12498)
        (fun uu____12503 ->
           let uu____12504 = cur_goal () in
           bind uu____12504
             (fun g ->
                let uu____12510 =
                  let uu____12519 = FStar_Tactics_Types.goal_env g in
                  __tc uu____12519 ty in
                bind uu____12510
                  (fun uu____12531 ->
                     match uu____12531 with
                     | (ty1, uu____12541, guard) ->
                         let uu____12543 =
                           let uu____12546 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____12546 guard in
                         bind uu____12543
                           (fun uu____12550 ->
                              let uu____12551 =
                                let uu____12555 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____12556 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____12555 uu____12556 ty1 in
                              bind uu____12551
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____12565 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     replace_cur uu____12565
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____12572 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____12573 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____12572
                                          uu____12573 in
                                      let nty =
                                        let uu____12575 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____12575 ty1 in
                                      let uu____12576 =
                                        let uu____12580 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____12580 ng nty in
                                      bind uu____12576
                                        (fun b ->
                                           if b
                                           then
                                             let uu____12589 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             replace_cur uu____12589
                                           else fail "not convertible"))))))) in
    FStar_All.pipe_left (wrap_err "change") uu____12492
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b -> fun msg -> fun k -> if b then fail msg else k ()
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm ->
    let uu____12663 =
      let uu____12672 = cur_goal () in
      bind uu____12672
        (fun g ->
           let uu____12684 =
             let uu____12693 = FStar_Tactics_Types.goal_env g in
             __tc uu____12693 s_tm in
           bind uu____12684
             (fun uu____12711 ->
                match uu____12711 with
                | (s_tm1, s_ty, guard) ->
                    let uu____12729 =
                      let uu____12732 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____12732 guard in
                    bind uu____12729
                      (fun uu____12745 ->
                         let uu____12746 =
                           FStar_Syntax_Util.head_and_args' s_ty in
                         match uu____12746 with
                         | (h, args) ->
                             let uu____12791 =
                               let uu____12798 =
                                 let uu____12799 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____12799.FStar_Syntax_Syntax.n in
                               match uu____12798 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12814;
                                      FStar_Syntax_Syntax.vars = uu____12815;_},
                                    us)
                                   -> ret (fv, us)
                               | uu____12825 -> fail "type is not an fv" in
                             bind uu____12791
                               (fun uu____12846 ->
                                  match uu____12846 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____12862 =
                                        let uu____12865 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12865 t_lid in
                                      (match uu____12862 with
                                       | FStar_Pervasives_Native.None ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid, t_us, t_ps, t_ty, mut,
                                                 c_lids)
                                                ->
                                                failwhen
                                                  ((FStar_List.length a_us)
                                                     <>
                                                     (FStar_List.length t_us))
                                                  "t_us don't match?"
                                                  (fun uu____12916 ->
                                                     let uu____12917 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty in
                                                     match uu____12917 with
                                                     | (t_ps1, t_ty1) ->
                                                         let uu____12932 =
                                                           mapM
                                                             (fun c_lid ->
                                                                let uu____12960
                                                                  =
                                                                  let uu____12963
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12963
                                                                    c_lid in
                                                                match uu____12960
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
                                                                    (_c_lid,
                                                                    c_us,
                                                                    c_ty,
                                                                    _t_lid,
                                                                    nparam,
                                                                    mut1) ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor) in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____13037
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____13042
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____13042
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____13065
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____13065
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____13108
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs in
                                                                    (match uu____13108
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs1) ->
                                                                    let uu____13181
                                                                    =
                                                                    let uu____13183
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp in
                                                                    Prims.op_Negation
                                                                    uu____13183 in
                                                                    failwhen
                                                                    uu____13181
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13202
                                                                    ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    } in
                                                                    let is_imp
                                                                    uu___5_13219
                                                                    =
                                                                    match uu___5_13219
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13223)
                                                                    -> true
                                                                    | 
                                                                    uu____13226
                                                                    -> false in
                                                                    let uu____13230
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____13230
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____13364
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13426
                                                                    ->
                                                                    match uu____13426
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____13446),
                                                                    (t,
                                                                    uu____13448))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs2 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs1 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13518
                                                                    ->
                                                                    match uu____13518
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____13545),
                                                                    (t,
                                                                    uu____13547))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13606
                                                                    ->
                                                                    match uu____13606
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs2 in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats)) in
                                                                    let env =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env s_ty in
                                                                    let uu____13661
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1871_13678
                                                                    = env in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1871_13678.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat in
                                                                    match uu____13661
                                                                    with
                                                                    | 
                                                                    (uu____13692,
                                                                    uu____13693,
                                                                    uu____13694,
                                                                    pat_t,
                                                                    uu____13696,
                                                                    _guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13703
                                                                    =
                                                                    let uu____13704
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13704 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13703 in
                                                                    let cod1
                                                                    =
                                                                    let uu____13709
                                                                    =
                                                                    let uu____13718
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____13718] in
                                                                    let uu____13737
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13709
                                                                    uu____13737 in
                                                                    let nty =
                                                                    let uu____13743
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13743 in
                                                                    let uu____13746
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty in
                                                                    bind
                                                                    uu____13746
                                                                    (fun
                                                                    uu____13776
                                                                    ->
                                                                    match uu____13776
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2 in
                                                                    let brt1
                                                                    =
                                                                    let uu____13803
                                                                    =
                                                                    let uu____13814
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____13814] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13803 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____13850
                                                                    =
                                                                    let uu____13861
                                                                    =
                                                                    let uu____13866
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2) in
                                                                    (fv1,
                                                                    uu____13866) in
                                                                    (g', br,
                                                                    uu____13861) in
                                                                    ret
                                                                    uu____13850))))))
                                                                    | 
                                                                    uu____13887
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids in
                                                         bind uu____12932
                                                           (fun goal_brs ->
                                                              let uu____13937
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs in
                                                              match uu____13937
                                                              with
                                                              | (goals, brs,
                                                                 infos) ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                  let uu____14010
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                  bind
                                                                    uu____14010
                                                                    (
                                                                    fun
                                                                    uu____14021
                                                                    ->
                                                                    let uu____14022
                                                                    =
                                                                    add_goals
                                                                    goals in
                                                                    bind
                                                                    uu____14022
                                                                    (fun
                                                                    uu____14032
                                                                    ->
                                                                    ret infos))))
                                            | uu____14039 ->
                                                fail "not an inductive type")))))) in
    FStar_All.pipe_left (wrap_err "destruct") uu____12663
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14088::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14118 = init xs in x :: uu____14118
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t ->
    let uu____14131 =
      let t1 = FStar_Syntax_Util.unascribe t in
      let t2 = FStar_Syntax_Util.un_uinst t1 in
      let t3 = FStar_Syntax_Util.unlazy_emb t2 in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4, uu____14140) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1, []) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
          let uu____14206 = last args in
          (match uu____14206 with
           | (a, q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q in
               let uu____14236 =
                 let uu____14237 =
                   let uu____14242 =
                     let uu____14243 =
                       let uu____14248 = init args in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14248 in
                     uu____14243 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos in
                   (uu____14242, (a, q')) in
                 FStar_Reflection_Data.Tv_App uu____14237 in
               FStar_All.pipe_left ret uu____14236)
      | FStar_Syntax_Syntax.Tm_abs ([], uu____14259, uu____14260) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
          let uu____14313 = FStar_Syntax_Subst.open_term bs t4 in
          (match uu____14313 with
           | (bs1, t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14355 =
                      let uu____14356 =
                        let uu____14361 = FStar_Syntax_Util.abs bs2 t5 k in
                        (b, uu____14361) in
                      FStar_Reflection_Data.Tv_Abs uu____14356 in
                    FStar_All.pipe_left ret uu____14355))
      | FStar_Syntax_Syntax.Tm_type uu____14364 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14389 ->
          let uu____14404 = FStar_Syntax_Util.arrow_one t3 in
          (match uu____14404 with
           | FStar_Pervasives_Native.Some (b, c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv in
          let uu____14435 = FStar_Syntax_Subst.open_term [b] t4 in
          (match uu____14435 with
           | (b', t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14488 -> failwith "impossible" in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14501 =
            let uu____14502 = FStar_Reflection_Basic.inspect_const c in
            FStar_Reflection_Data.Tv_Const uu____14502 in
          FStar_All.pipe_left ret uu____14501
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
          let uu____14523 =
            let uu____14524 =
              let uu____14529 =
                let uu____14530 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_BigInt.of_int_fs uu____14530 in
              (uu____14529, (ctx_u, s)) in
            FStar_Reflection_Data.Tv_Uvar uu____14524 in
          FStar_All.pipe_left ret uu____14523
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14570 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv in
                 let uu____14575 = FStar_Syntax_Subst.open_term [b] t21 in
                 (match uu____14575 with
                  | (bs, t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14628 ->
                            failwith
                              "impossible: open_term returned different amount of binders" in
                      FStar_All.pipe_left ret
                        (FStar_Reflection_Data.Tv_Let
                           (false, (FStar_Pervasives_Native.fst b1),
                             (lb.FStar_Syntax_Syntax.lbdef), t22))))
      | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14670 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14674 = FStar_Syntax_Subst.open_let_rec [lb] t21 in
                 (match uu____14674 with
                  | (lbs, t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14694 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14700 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14755 = FStar_Reflection_Basic.inspect_const c in
                FStar_Reflection_Data.Pat_Constant uu____14755
            | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                let uu____14776 =
                  let uu____14783 =
                    FStar_List.map
                      (fun uu____14796 ->
                         match uu____14796 with
                         | (p1, uu____14805) -> inspect_pat p1) ps in
                  (fv, uu____14783) in
                FStar_Reflection_Data.Pat_Cons uu____14776
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
          let brs2 =
            FStar_List.map
              (fun uu___6_14901 ->
                 match uu___6_14901 with
                 | (pat, uu____14923, t5) ->
                     let uu____14941 = inspect_pat pat in (uu____14941, t5))
              brs1 in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14950 ->
          ((let uu____14952 =
              let uu____14958 =
                let uu____14960 = FStar_Syntax_Print.tag_of_term t3 in
                let uu____14962 = FStar_Syntax_Print.term_to_string t3 in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14960 uu____14962 in
              (FStar_Errors.Warning_CantInspect, uu____14958) in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14952);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown) in
    wrap_err "inspect" uu____14131
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14980 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left ret uu____14980
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14984 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left ret uu____14984
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14988 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left ret uu____14988
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____14995 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left ret uu____14995
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____15020 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left ret uu____15020
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____15037 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left ret uu____15037
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____15056 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left ret uu____15056
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15060 =
          let uu____15061 =
            let uu____15068 =
              let uu____15069 = FStar_Reflection_Basic.pack_const c in
              FStar_Syntax_Syntax.Tm_constant uu____15069 in
            FStar_Syntax_Syntax.mk uu____15068 in
          uu____15061 FStar_Pervasives_Native.None FStar_Range.dummyRange in
        FStar_All.pipe_left ret uu____15060
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____15074 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange in
        FStar_All.pipe_left ret uu____15074
    | FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange in
        let uu____15085 =
          let uu____15086 =
            let uu____15093 =
              let uu____15094 =
                let uu____15108 =
                  let uu____15111 =
                    let uu____15112 = FStar_Syntax_Syntax.mk_binder bv in
                    [uu____15112] in
                  FStar_Syntax_Subst.close uu____15111 t2 in
                ((false, [lb]), uu____15108) in
              FStar_Syntax_Syntax.Tm_let uu____15094 in
            FStar_Syntax_Syntax.mk uu____15093 in
          uu____15086 FStar_Pervasives_Native.None FStar_Range.dummyRange in
        FStar_All.pipe_left ret uu____15085
    | FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange in
        let uu____15154 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____15154 with
         | (lbs, body) ->
             let uu____15169 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange in
             FStar_All.pipe_left ret uu____15169)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15206 =
                let uu____15207 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____15207 in
              FStar_All.pipe_left wrap uu____15206
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____15214 =
                let uu____15215 =
                  let uu____15229 =
                    FStar_List.map
                      (fun p1 ->
                         let uu____15247 = pack_pat p1 in
                         (uu____15247, false)) ps in
                  (fv, uu____15229) in
                FStar_Syntax_Syntax.Pat_cons uu____15215 in
              FStar_All.pipe_left wrap uu____15214
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___7_15296 ->
               match uu___7_15296 with
               | (pat, t1) ->
                   let uu____15313 = pack_pat pat in
                   (uu____15313, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____15361 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange in
        FStar_All.pipe_left ret uu____15361
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____15389 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange in
        FStar_All.pipe_left ret uu____15389
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____15435 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange in
        FStar_All.pipe_left ret uu____15435
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____15474 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange in
        FStar_All.pipe_left ret uu____15474
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty ->
    fun k ->
      let uu____15494 =
        bind get
          (fun ps ->
             let uu____15500 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____15500 with
             | FStar_Pervasives_Native.None -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (wrap_err "lget") uu____15494
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____15534 =
          bind get
            (fun ps ->
               let ps1 =
                 let uu___2169_15541 = ps in
                 let uu____15542 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2169_15541.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2169_15541.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2169_15541.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2169_15541.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2169_15541.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2169_15541.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2169_15541.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2169_15541.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2169_15541.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2169_15541.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2169_15541.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2169_15541.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15542
                 } in
               set ps1) in
        FStar_All.pipe_left (wrap_err "lset") uu____15534
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun typ ->
      let uu____15569 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____15569 with
      | (u, ctx_uvars, g_u) ->
          let uu____15602 = FStar_List.hd ctx_uvars in
          (match uu____15602 with
           | (ctx_uvar, uu____15616) ->
               let g =
                 let uu____15618 = FStar_Options.peek () in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15618 false
                   "" in
               (g, g_u))
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env ->
      fun typ ->
        let uu____15641 = goal_of_goal_ty env typ in
        match uu____15641 with
        | (g, g_u) ->
            let ps =
              let uu____15653 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose") in
              let uu____15656 = FStar_Util.psmap_empty () in
              {
                FStar_Tactics_Types.main_context = env;
                FStar_Tactics_Types.main_goal = g;
                FStar_Tactics_Types.all_implicits =
                  (g_u.FStar_TypeChecker_Env.implicits);
                FStar_Tactics_Types.goals = [g];
                FStar_Tactics_Types.smt_goals = [];
                FStar_Tactics_Types.depth = (Prims.parse_int "0");
                FStar_Tactics_Types.__dump =
                  (fun ps -> fun msg -> dump_proofstate ps msg);
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____15653;
                FStar_Tactics_Types.local_state = uu____15656
              } in
            let uu____15666 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____15666)