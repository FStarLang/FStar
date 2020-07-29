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
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> FStar_TypeChecker_Normalize.unfold_whnf e t
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu____58 =
      let uu____59 = FStar_Tactics_Types.goal_env g in
      let uu____60 = FStar_Tactics_Types.goal_type g in
      bnorm uu____59 uu____60 in
    FStar_Tactics_Types.goal_with_type g uu____58
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu____76 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____76
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu____92 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____92
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu____113 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____113
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu____124 =
       let uu____125 = FStar_Options.silent () in Prims.op_Negation uu____125 in
     if uu____124 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____133 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu____139 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu____139)
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst = FStar_TypeChecker_Cfg.psc_subst psc in
         (let uu____157 = FStar_Tactics_Types.subst_proof_state subst ps in
          FStar_Tactics_Printing.do_dump_proofstate uu____157 msg);
         FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuuu164 .
    Prims.string -> Prims.string -> 'uuuuuu164 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      let uu____177 = FStar_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu____177
let fail2 :
  'uuuuuu186 .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuuu186 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu____204 = FStar_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu____204
let fail3 :
  'uuuuuu215 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuuu215 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____238 = FStar_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu____238
let fail4 :
  'uuuuuu251 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuuu251 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____279 = FStar_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu____279
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____312 = FStar_Tactics_Monad.run t ps in
         match uu____312 with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___68_336 = ps in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___68_336.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___68_336.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___68_336.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___68_336.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___68_336.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___68_336.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___68_336.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___68_336.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___68_336.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___68_336.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___68_336.FStar_Tactics_Types.local_state)
                 } in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
let recover :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let uu____374 = FStar_Tactics_Monad.run t ps in
         match uu____374 with
         | FStar_Tactics_Result.Success (a1, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q)
         | FStar_Tactics_Result.Failed (m, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
let trytac :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    let uu____421 = catch t in
    FStar_Tactics_Monad.bind uu____421
      (fun r ->
         match r with
         | FStar_Util.Inr v ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v)
         | FStar_Util.Inl uu____448 ->
             FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
let trytac_exn :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         try
           (fun uu___94_479 ->
              match () with
              | () ->
                  let uu____484 = trytac t in
                  FStar_Tactics_Monad.run uu____484 ps) ()
         with
         | FStar_Errors.Err (uu____500, msg) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____504 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____509, msg, uu____511) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____514 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____536 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____536 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu____546::(e1, FStar_Pervasives_Native.None)::(e2,
                                                         FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____606::uu____607::(e1, uu____609)::(e2, uu____611)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____688 ->
        let uu____691 = FStar_Syntax_Util.unb2t typ in
        (match uu____691 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____705 = FStar_Syntax_Util.head_and_args t in
             (match uu____705 with
              | (hd, args) ->
                  let uu____754 =
                    let uu____769 =
                      let uu____770 = FStar_Syntax_Subst.compress hd in
                      uu____770.FStar_Syntax_Syntax.n in
                    (uu____769, args) in
                  (match uu____754 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu____790, FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____791))::(e1,
                                                                   FStar_Pervasives_Native.None)::
                      (e2, FStar_Pervasives_Native.None)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____858 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____894 = destruct_eq' typ in
    match uu____894 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____924 = FStar_Syntax_Util.un_squash typ in
        (match uu____924 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        (let uu____966 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
         if uu____966
         then
           let uu____967 = FStar_Syntax_Print.term_to_string t1 in
           let uu____968 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____967
             uu____968
         else ());
        (try
           (fun uu___170_975 ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env1 t1 t2 in
                  ((let uu____982 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____982
                    then
                      let uu____983 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env1) res in
                      let uu____984 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____985 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____983
                        uu____984 uu____985
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____990 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits in
                        FStar_Tactics_Monad.bind uu____990
                          (fun uu____994 -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____1001, msg) ->
             FStar_Tactics_Monad.mlog
               (fun uu____1004 ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1006 -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____1007, msg, r) ->
             FStar_Tactics_Monad.mlog
               (fun uu____1012 ->
                  let uu____1013 = FStar_Range.string_of_range r in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1013)
               (fun uu____1015 -> FStar_Tactics_Monad.ret false))
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____1038 ->
             (let uu____1040 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
              if uu____1040
              then
                (FStar_Options.push ();
                 (let uu____1042 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck" in
                  ()))
              else ());
             (let uu____1044 =
                __do_unify
                  (let uu___205_1049 = env1 in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___205_1049.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___205_1049.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___205_1049.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___205_1049.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___205_1049.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___205_1049.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___205_1049.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___205_1049.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___205_1049.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___205_1049.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___205_1049.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___205_1049.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___205_1049.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___205_1049.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___205_1049.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___205_1049.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___205_1049.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___205_1049.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___205_1049.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___205_1049.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (uu___205_1049.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___205_1049.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___205_1049.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___205_1049.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___205_1049.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___205_1049.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___205_1049.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___205_1049.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___205_1049.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___205_1049.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___205_1049.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___205_1049.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___205_1049.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___205_1049.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___205_1049.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___205_1049.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___205_1049.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___205_1049.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___205_1049.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___205_1049.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___205_1049.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___205_1049.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___205_1049.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___205_1049.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___205_1049.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___205_1049.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac = false
                   }) t1 t2 in
              FStar_Tactics_Monad.bind uu____1044
                (fun r ->
                   (let uu____1054 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____1054 then FStar_Options.pop () else ());
                   FStar_Tactics_Monad.ret r)))
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____1075 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____1075
          (fun tx ->
             let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
             let uu____1089 = do_unify env1 t1 t2 in
             FStar_Tactics_Monad.bind uu____1089
               (fun r ->
                  if r
                  then
                    let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
                    let uu____1102 =
                      let uu____1103 = FStar_Util.set_eq uvs1 uvs2 in
                      Prims.op_Negation uu____1103 in
                    (if uu____1102
                     then
                       (FStar_Syntax_Unionfind.rollback tx;
                        FStar_Tactics_Monad.ret false)
                     else FStar_Tactics_Monad.ret true)
                  else FStar_Tactics_Monad.ret false))
let (do_match_on_lhs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____1128 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____1128
          (fun tx ->
             let uu____1138 = destruct_eq t1 in
             match uu____1138 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "do_match_on_lhs: not an eq"
             | FStar_Pervasives_Native.Some (lhs, uu____1152) ->
                 let uvs1 = FStar_Syntax_Free.uvars_uncached lhs in
                 let uu____1160 = do_unify env1 t1 t2 in
                 FStar_Tactics_Monad.bind uu____1160
                   (fun r ->
                      if r
                      then
                        let uvs2 = FStar_Syntax_Free.uvars_uncached lhs in
                        let uu____1173 =
                          let uu____1174 = FStar_Util.set_eq uvs1 uvs2 in
                          Prims.op_Negation uu____1174 in
                        (if uu____1173
                         then
                           (FStar_Syntax_Unionfind.rollback tx;
                            FStar_Tactics_Monad.ret false)
                         else FStar_Tactics_Monad.ret true)
                      else FStar_Tactics_Monad.ret false))
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1194 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____1194 with
      | FStar_Pervasives_Native.Some uu____1199 ->
          let uu____1200 =
            let uu____1201 =
              FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____1201 in
          FStar_Tactics_Monad.fail uu____1200
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           FStar_Tactics_Monad.ret ())
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1217 = FStar_Tactics_Types.goal_env goal in
      let uu____1218 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____1217 solution uu____1218
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu____1237 ->
           let uu____1238 =
             let uu____1239 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____1239 in
           let uu____1240 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____1238 uu____1240)
        (fun uu____1243 ->
           let uu____1244 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu____1244
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____1252 ->
                       FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____1254 =
                     let uu____1255 =
                       let uu____1256 = FStar_Tactics_Types.goal_env goal in
                       tts uu____1256 solution in
                     let uu____1257 =
                       let uu____1258 = FStar_Tactics_Types.goal_env goal in
                       let uu____1259 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____1258 uu____1259 in
                     let uu____1260 =
                       let uu____1261 = FStar_Tactics_Types.goal_env goal in
                       let uu____1262 = FStar_Tactics_Types.goal_type goal in
                       tts uu____1261 uu____1262 in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1255 uu____1257 uu____1260 in
                   FStar_Tactics_Monad.fail uu____1254)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1277 = set_solution goal solution in
      FStar_Tactics_Monad.bind uu____1277
        (fun uu____1281 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____1283 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1290 = FStar_Syntax_Util.un_squash t1 in
    match uu____1290 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____1301 =
          let uu____1302 = FStar_Syntax_Subst.compress t'1 in
          uu____1302.FStar_Syntax_Syntax.n in
        (match uu____1301 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1306 -> false)
    | uu____1307 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1317 = FStar_Syntax_Util.un_squash t in
    match uu____1317 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1327 =
          let uu____1328 = FStar_Syntax_Subst.compress t' in
          uu____1328.FStar_Syntax_Syntax.n in
        (match uu____1327 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1332 -> false)
    | uu____1333 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____1347 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu____1356 =
                   let uu____1357 = FStar_Tactics_Types.goal_type g in
                   uu____1357.FStar_Syntax_Syntax.pos in
                 let uu____1360 =
                   let uu____1365 =
                     let uu____1366 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1366 in
                   (FStar_Errors.Warning_TacAdmit, uu____1365) in
                 FStar_Errors.log_issue uu____1356 uu____1360);
                solve' g t)) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____1347
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1381 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___279_1391 = ps in
           {
             FStar_Tactics_Types.main_context =
               (uu___279_1391.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___279_1391.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___279_1391.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___279_1391.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___279_1391.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___279_1391.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___279_1391.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___279_1391.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___279_1391.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___279_1391.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___279_1391.FStar_Tactics_Types.local_state)
           } in
         let uu____1392 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu____1392
           (fun uu____1397 ->
              let uu____1398 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu____1398))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1405 ->
    let uu____1408 =
      let uu____1409 = FStar_Util.now_ms () in
      FStar_All.pipe_right uu____1409 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu____1408
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1452 ->
                let uu____1453 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1453)
             (fun uu____1456 ->
                let e1 =
                  let uu___288_1458 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___288_1458.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___288_1458.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___288_1458.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___288_1458.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___288_1458.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___288_1458.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___288_1458.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___288_1458.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___288_1458.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___288_1458.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___288_1458.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___288_1458.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___288_1458.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___288_1458.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___288_1458.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___288_1458.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___288_1458.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___288_1458.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___288_1458.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___288_1458.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___288_1458.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___288_1458.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___288_1458.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___288_1458.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___288_1458.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___288_1458.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___288_1458.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___288_1458.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___288_1458.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___288_1458.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___288_1458.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___288_1458.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___288_1458.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___288_1458.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___288_1458.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___288_1458.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___288_1458.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___288_1458.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___288_1458.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___288_1458.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___288_1458.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___288_1458.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___288_1458.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___288_1458.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___288_1458.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___288_1458.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___292_1469 ->
                     match () with
                     | () ->
                         let uu____1478 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         FStar_Tactics_Monad.ret uu____1478) ()
                with
                | FStar_Errors.Err (uu____1505, msg) ->
                    let uu____1507 = tts e1 t in
                    let uu____1508 =
                      let uu____1509 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1509
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1507 uu____1508 msg
                | FStar_Errors.Error (uu____1516, msg, uu____1518) ->
                    let uu____1519 = tts e1 t in
                    let uu____1520 =
                      let uu____1521 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1521
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1519 uu____1520 msg))
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1570 ->
                let uu____1571 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1571)
             (fun uu____1574 ->
                let e1 =
                  let uu___309_1576 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___309_1576.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___309_1576.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___309_1576.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___309_1576.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___309_1576.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___309_1576.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___309_1576.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___309_1576.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___309_1576.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___309_1576.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___309_1576.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___309_1576.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___309_1576.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___309_1576.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___309_1576.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___309_1576.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___309_1576.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___309_1576.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___309_1576.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___309_1576.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___309_1576.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___309_1576.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___309_1576.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___309_1576.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___309_1576.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___309_1576.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___309_1576.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___309_1576.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___309_1576.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___309_1576.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___309_1576.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___309_1576.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___309_1576.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___309_1576.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___309_1576.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___309_1576.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___309_1576.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___309_1576.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___309_1576.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___309_1576.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___309_1576.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___309_1576.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___309_1576.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___309_1576.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___309_1576.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___309_1576.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___313_1590 ->
                     match () with
                     | () ->
                         let uu____1599 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____1599 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1637, msg) ->
                    let uu____1639 = tts e1 t in
                    let uu____1640 =
                      let uu____1641 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1641
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1639 uu____1640 msg
                | FStar_Errors.Error (uu____1648, msg, uu____1650) ->
                    let uu____1651 = tts e1 t in
                    let uu____1652 =
                      let uu____1653 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1653
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1651 uu____1652 msg))
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1702 ->
                let uu____1703 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1703)
             (fun uu____1707 ->
                let e1 =
                  let uu___334_1709 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___334_1709.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___334_1709.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___334_1709.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___334_1709.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___334_1709.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___334_1709.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___334_1709.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___334_1709.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___334_1709.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___334_1709.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___334_1709.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___334_1709.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___334_1709.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___334_1709.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___334_1709.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___334_1709.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___334_1709.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___334_1709.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___334_1709.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___334_1709.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___334_1709.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___334_1709.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___334_1709.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___334_1709.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___334_1709.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___334_1709.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___334_1709.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___334_1709.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___334_1709.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___334_1709.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___334_1709.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___334_1709.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___334_1709.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___334_1709.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___334_1709.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___334_1709.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___334_1709.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___334_1709.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___334_1709.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___334_1709.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___334_1709.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___334_1709.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___334_1709.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___334_1709.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___334_1709.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___334_1709.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                let e2 =
                  let uu___337_1711 = e1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___337_1711.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___337_1711.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___337_1711.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___337_1711.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___337_1711.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___337_1711.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___337_1711.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___337_1711.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___337_1711.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___337_1711.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___337_1711.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___337_1711.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___337_1711.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___337_1711.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___337_1711.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___337_1711.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___337_1711.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___337_1711.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___337_1711.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___337_1711.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___337_1711.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___337_1711.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___337_1711.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___337_1711.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___337_1711.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___337_1711.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___337_1711.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___337_1711.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___337_1711.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___337_1711.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___337_1711.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___337_1711.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___337_1711.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___337_1711.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___337_1711.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___337_1711.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___337_1711.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___337_1711.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___337_1711.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___337_1711.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___337_1711.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___337_1711.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___337_1711.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___337_1711.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___337_1711.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___337_1711.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___341_1722 ->
                     match () with
                     | () ->
                         let uu____1731 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu____1731) ()
                with
                | FStar_Errors.Err (uu____1758, msg) ->
                    let uu____1760 = tts e2 t in
                    let uu____1761 =
                      let uu____1762 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1762
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1760 uu____1761 msg
                | FStar_Errors.Error (uu____1769, msg, uu____1771) ->
                    let uu____1772 = tts e2 t in
                    let uu____1773 =
                      let uu____1774 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1774
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1772 uu____1773 msg))
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
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu____1801 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           (let uu___362_1819 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_1819.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___362_1819.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___362_1819.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___362_1819.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_1819.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_1819.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_1819.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_1819.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___362_1819.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_1819.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___362_1819.FStar_Tactics_Types.local_state)
            }))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu____1843 = get_guard_policy () in
      FStar_Tactics_Monad.bind uu____1843
        (fun old_pol ->
           let uu____1849 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu____1849
             (fun uu____1853 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu____1857 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu____1857
                       (fun uu____1861 -> FStar_Tactics_Monad.ret r))))
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1864 = trytac FStar_Tactics_Monad.cur_goal in
  FStar_Tactics_Monad.bind uu____1864
    (fun uu___0_1873 ->
       match uu___0_1873 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____1879 = FStar_Options.peek () in
           FStar_Tactics_Monad.ret uu____1879)
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun g ->
        FStar_Tactics_Monad.mlog
          (fun uu____1901 ->
             let uu____1902 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1902)
          (fun uu____1905 ->
             let uu____1906 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits in
             FStar_Tactics_Monad.bind uu____1906
               (fun uu____1910 ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts ->
                       let uu____1914 =
                         let uu____1915 =
                           FStar_TypeChecker_Rel.simplify_guard e g in
                         uu____1915.FStar_TypeChecker_Common.guard_f in
                       match uu____1914 with
                       | FStar_TypeChecker_Common.Trivial ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1919 = istrivial e f in
                           if uu____1919
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu____1929 =
                                          let uu____1934 =
                                            let uu____1935 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1935 in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1934) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1929);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1938 ->
                                           let uu____1939 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1939)
                                        (fun uu____1942 ->
                                           let uu____1943 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1943
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___391_1950 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___391_1950.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___391_1950.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___391_1950.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___391_1950.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1953 ->
                                           let uu____1954 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____1954)
                                        (fun uu____1957 ->
                                           let uu____1958 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1958
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___398_1965 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___398_1965.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___398_1965.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___398_1965.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___398_1965.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1968 ->
                                           let uu____1969 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____1969)
                                        (fun uu____1971 ->
                                           try
                                             (fun uu___405_1976 ->
                                                match () with
                                                | () ->
                                                    let uu____1979 =
                                                      let uu____1980 =
                                                        let uu____1981 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____1981 in
                                                      Prims.op_Negation
                                                        uu____1980 in
                                                    if uu____1979
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____1986 ->
                                                           let uu____1987 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____1987)
                                                        (fun uu____1989 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___404_1992 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____1997 ->
                                                    let uu____1998 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____1998)
                                                 (fun uu____2000 ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____2015 =
        let uu____2018 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu____2018
          (fun uu____2038 ->
             match uu____2038 with
             | (uu____2047, lc, uu____2049) ->
                 let uu____2050 =
                   let uu____2051 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_All.pipe_right uu____2051
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu____2050) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____2015
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____2078 =
        let uu____2083 = tcc e t in
        FStar_Tactics_Monad.bind uu____2083
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____2078
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2106 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____2112 =
           let uu____2113 = FStar_Tactics_Types.goal_env goal in
           let uu____2114 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____2113 uu____2114 in
         if uu____2112
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2118 =
              let uu____2119 = FStar_Tactics_Types.goal_env goal in
              let uu____2120 = FStar_Tactics_Types.goal_type goal in
              tts uu____2119 uu____2120 in
            fail1 "Not a trivial goal: %s" uu____2118))
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac ->
        'b FStar_Tactics_Monad.tac -> ('a * 'b) FStar_Tactics_Monad.tac
  =
  fun n ->
    fun l ->
      fun r ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun p ->
             let uu____2169 =
               try
                 (fun uu___456_2192 ->
                    match () with
                    | () ->
                        let uu____2203 =
                          let uu____2212 = FStar_BigInt.to_int_fs n in
                          FStar_List.splitAt uu____2212
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu____2203) ()
               with
               | uu___455_2222 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu____2169
               (fun uu____2258 ->
                  match uu____2258 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___438_2284 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___438_2284.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___438_2284.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___438_2284.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___438_2284.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___438_2284.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___438_2284.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___438_2284.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___438_2284.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___438_2284.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___438_2284.FStar_Tactics_Types.local_state)
                        } in
                      let uu____2285 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu____2285
                        (fun uu____2293 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       let uu___444_2309 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___444_2309.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___444_2309.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___444_2309.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___444_2309.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___444_2309.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___444_2309.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___444_2309.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___444_2309.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___444_2309.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___444_2309.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____2310 =
                                       FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu____2310
                                       (fun uu____2318 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___450_2334 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___450_2334.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___450_2334.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____2335 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu____2335
                                                      (fun uu____2343 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____2349 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu____2370 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu____2370
      (fun uu____2383 ->
         match uu____2383 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____2420::uu____2421 ->
             let uu____2424 =
               let uu____2433 = map tau in
               divide FStar_BigInt.one tau uu____2433 in
             FStar_Tactics_Monad.bind uu____2424
               (fun uu____2451 ->
                  match uu____2451 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu____2492 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2497 ->
             let uu____2498 = map t2 in
             FStar_Tactics_Monad.bind uu____2498
               (fun uu____2506 -> FStar_Tactics_Monad.ret ())) in
      focus uu____2492
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2515 ->
    let uu____2518 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____2527 =
             let uu____2534 =
               let uu____2535 = FStar_Tactics_Types.goal_env goal in
               let uu____2536 = FStar_Tactics_Types.goal_type goal in
               whnf uu____2535 uu____2536 in
             FStar_Syntax_Util.arrow_one uu____2534 in
           match uu____2527 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____2545 =
                 let uu____2546 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____2546 in
               if uu____2545
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2551 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____2551 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____2567 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' in
                  FStar_Tactics_Monad.bind uu____2567
                    (fun uu____2583 ->
                       match uu____2583 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____2607 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu____2607
                             (fun uu____2613 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____2615 =
                                  let uu____2618 = bnorm_goal g in
                                  FStar_Tactics_Monad.replace_cur uu____2618 in
                                FStar_Tactics_Monad.bind uu____2615
                                  (fun uu____2620 ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____2625 =
                 let uu____2626 = FStar_Tactics_Types.goal_env goal in
                 let uu____2627 = FStar_Tactics_Types.goal_type goal in
                 tts uu____2626 uu____2627 in
               fail1 "goal is not an arrow (%s)" uu____2625) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2518
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2642 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2663 =
            let uu____2670 =
              let uu____2671 = FStar_Tactics_Types.goal_env goal in
              let uu____2672 = FStar_Tactics_Types.goal_type goal in
              whnf uu____2671 uu____2672 in
            FStar_Syntax_Util.arrow_one uu____2670 in
          match uu____2663 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____2685 =
                let uu____2686 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____2686 in
              if uu____2685
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2699 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2699 in
                 let bs =
                   let uu____2709 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2709; b] in
                 let env' =
                   let uu____2735 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____2735 bs in
                 let uu____2736 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 FStar_Tactics_Monad.bind uu____2736
                   (fun uu____2761 ->
                      match uu____2761 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____2775 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____2778 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2775
                              FStar_Parser_Const.effect_Tot_lid uu____2778 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____2796 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____2796 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____2818 =
                                   let uu____2819 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____2819.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu____2818 in
                               let uu____2832 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu____2832
                                 (fun uu____2841 ->
                                    let uu____2842 =
                                      let uu____2845 =
                                        bnorm_goal
                                          (let uu___521_2848 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___521_2848.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___521_2848.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___521_2848.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___521_2848.FStar_Tactics_Types.label)
                                           }) in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2845 in
                                    FStar_Tactics_Monad.bind uu____2842
                                      (fun uu____2855 ->
                                         let uu____2856 =
                                           let uu____2861 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____2861, b) in
                                         FStar_Tactics_Monad.ret uu____2856)))))
          | FStar_Pervasives_Native.None ->
              let uu____2870 =
                let uu____2871 = FStar_Tactics_Types.goal_env goal in
                let uu____2872 = FStar_Tactics_Types.goal_type goal in
                tts uu____2871 uu____2872 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2870))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____2894 ->
              let uu____2895 =
                let uu____2896 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____2896 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2895)
           (fun uu____2901 ->
              let steps =
                let uu____2905 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2905 in
              let t =
                let uu____2909 = FStar_Tactics_Types.goal_env goal in
                let uu____2910 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____2909 uu____2910 in
              let uu____2911 = FStar_Tactics_Types.goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu____2911))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____2935 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2943 -> g.FStar_Tactics_Types.opts
                 | uu____2946 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu____2951 ->
                    let uu____2952 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2952)
                 (fun uu____2955 ->
                    let uu____2956 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu____2956
                      (fun uu____2977 ->
                         match uu____2977 with
                         | (t1, uu____2987, uu____2988) ->
                             let steps =
                               let uu____2992 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____2992 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu____2998 ->
                                  let uu____2999 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____2999)
                               (fun uu____3001 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2935
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____3012 ->
    let uu____3015 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____3022 =
             let uu____3033 = FStar_Tactics_Types.goal_env g in
             let uu____3034 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____3033 uu____3034 in
           match uu____3022 with
           | (uu____3037, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____3062 =
                 let uu____3067 =
                   let uu____3072 =
                     let uu____3073 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____3073] in
                   FStar_Syntax_Subst.open_term uu____3072 phi in
                 match uu____3067 with
                 | (bvs, phi1) ->
                     let uu____3098 =
                       let uu____3099 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____3099 in
                     (uu____3098, phi1) in
               (match uu____3062 with
                | (bv1, phi1) ->
                    let uu____3118 =
                      let uu____3121 = FStar_Tactics_Types.goal_env g in
                      let uu____3122 =
                        let uu____3123 =
                          let uu____3126 =
                            let uu____3127 =
                              let uu____3134 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____3134) in
                            FStar_Syntax_Syntax.NT uu____3127 in
                          [uu____3126] in
                        FStar_Syntax_Subst.subst uu____3123 phi1 in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____3121 uu____3122
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    FStar_Tactics_Monad.bind uu____3118
                      (fun g2 ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____3142 ->
                              FStar_Tactics_Monad.add_goals [g1; g2])))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____3015
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu____3166 = FStar_Tactics_Types.goal_env goal in
               let uu____3167 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____3166 uu____3167
             else FStar_Tactics_Types.goal_env goal in
           let uu____3169 = __tc env1 t in
           FStar_Tactics_Monad.bind uu____3169
             (fun uu____3188 ->
                match uu____3188 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____3203 ->
                         let uu____3204 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____3205 =
                           let uu____3206 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____3206
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3204 uu____3205)
                      (fun uu____3209 ->
                         let uu____3210 =
                           let uu____3213 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____3213 guard in
                         FStar_Tactics_Monad.bind uu____3210
                           (fun uu____3215 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____3219 ->
                                   let uu____3220 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____3221 =
                                     let uu____3222 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3222 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3220 uu____3221)
                                (fun uu____3225 ->
                                   let uu____3226 =
                                     let uu____3229 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____3230 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____3229 typ uu____3230 in
                                   FStar_Tactics_Monad.bind uu____3226
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3236 =
                                             let uu____3241 =
                                               let uu____3246 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu____3246 in
                                             let uu____3247 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____3241 typ uu____3247 in
                                           match uu____3236 with
                                           | (typ1, goalt) ->
                                               let uu____3252 =
                                                 let uu____3253 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu____3253 t1 in
                                               let uu____3254 =
                                                 let uu____3255 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu____3256 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu____3255 uu____3256 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____3252 typ1 goalt
                                                 uu____3254)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu____3276 =
          FStar_Tactics_Monad.mlog
            (fun uu____3281 ->
               let uu____3282 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3282)
            (fun uu____3285 ->
               let uu____3286 =
                 let uu____3293 = __exact_now set_expected_typ tm in
                 catch uu____3293 in
               FStar_Tactics_Monad.bind uu____3286
                 (fun uu___2_3302 ->
                    match uu___2_3302 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____3313 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3316 ->
                             let uu____3317 =
                               let uu____3324 =
                                 let uu____3327 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu____3327
                                   (fun uu____3332 ->
                                      let uu____3333 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu____3333
                                        (fun uu____3337 ->
                                           __exact_now set_expected_typ tm)) in
                               catch uu____3324 in
                             FStar_Tactics_Monad.bind uu____3317
                               (fun uu___1_3344 ->
                                  match uu___1_3344 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3353 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3355 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____3356 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3358 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3360 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____3276
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list
              FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun acc ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            let f = if only_match then do_match else do_unify in
            let uu____3453 = f e ty2 ty1 in
            FStar_Tactics_Monad.bind uu____3453
              (fun uu___3_3465 ->
                 if uu___3_3465
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3484 = FStar_Syntax_Util.arrow_one ty1 in
                    match uu____3484 with
                    | FStar_Pervasives_Native.None ->
                        let uu____3505 = term_to_string e ty1 in
                        let uu____3506 = term_to_string e ty2 in
                        fail2 "Could not instantiate, %s to %s" uu____3505
                          uu____3506
                    | FStar_Pervasives_Native.Some (b, c) ->
                        let uu____3521 =
                          let uu____3522 = FStar_Syntax_Util.is_total_comp c in
                          Prims.op_Negation uu____3522 in
                        if uu____3521
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3542 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           FStar_Tactics_Monad.bind uu____3542
                             (fun uu____3566 ->
                                match uu____3566 with
                                | (uvt, uv) ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu____3593 ->
                                         let uu____3594 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____3594)
                                      (fun uu____3598 ->
                                         let typ =
                                           FStar_Syntax_Util.comp_result c in
                                         let typ' =
                                           FStar_Syntax_Subst.subst
                                             [FStar_Syntax_Syntax.NT
                                                ((FStar_Pervasives_Native.fst
                                                    b), uvt)] typ in
                                         __try_unify_by_application
                                           only_match
                                           ((uvt,
                                              (FStar_Pervasives_Native.snd b),
                                              uv) :: acc) e typ' ty2)))))
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun e ->
      fun ty1 ->
        fun ty2 -> __try_unify_by_application only_match [] e ty1 ty2
let (t_apply :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tm ->
        let uu____3680 =
          FStar_Tactics_Monad.mlog
            (fun uu____3685 ->
               let uu____3686 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3686)
            (fun uu____3688 ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal ->
                    let e = FStar_Tactics_Types.goal_env goal in
                    FStar_Tactics_Monad.mlog
                      (fun uu____3697 ->
                         let uu____3698 =
                           FStar_Syntax_Print.term_to_string tm in
                         let uu____3699 =
                           FStar_Tactics_Printing.goal_to_string_verbose goal in
                         let uu____3700 =
                           FStar_TypeChecker_Env.print_gamma
                             e.FStar_TypeChecker_Env.gamma in
                         FStar_Util.print3
                           "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                           uu____3698 uu____3699 uu____3700)
                      (fun uu____3703 ->
                         let uu____3704 = __tc e tm in
                         FStar_Tactics_Monad.bind uu____3704
                           (fun uu____3725 ->
                              match uu____3725 with
                              | (tm1, typ, guard) ->
                                  let typ1 = bnorm e typ in
                                  let uu____3738 =
                                    let uu____3749 =
                                      FStar_Tactics_Types.goal_type goal in
                                    try_unify_by_application only_match e
                                      typ1 uu____3749 in
                                  FStar_Tactics_Monad.bind uu____3738
                                    (fun uvs ->
                                       FStar_Tactics_Monad.mlog
                                         (fun uu____3770 ->
                                            let uu____3771 =
                                              FStar_Common.string_of_list
                                                (fun uu____3782 ->
                                                   match uu____3782 with
                                                   | (t, uu____3790,
                                                      uu____3791) ->
                                                       FStar_Syntax_Print.term_to_string
                                                         t) uvs in
                                            FStar_Util.print1
                                              "t_apply: found args = %s\n"
                                              uu____3771)
                                         (fun uu____3798 ->
                                            let fix_qual q =
                                              match q with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.Meta
                                                  uu____3813) ->
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       false)
                                              | uu____3814 -> q in
                                            let w =
                                              FStar_List.fold_right
                                                (fun uu____3837 ->
                                                   fun w ->
                                                     match uu____3837 with
                                                     | (uvt, q, uu____3855)
                                                         ->
                                                         FStar_Syntax_Util.mk_app
                                                           w
                                                           [(uvt,
                                                              (fix_qual q))])
                                                uvs tm1 in
                                            let uvset =
                                              let uu____3887 =
                                                FStar_Syntax_Free.new_uv_set
                                                  () in
                                              FStar_List.fold_right
                                                (fun uu____3904 ->
                                                   fun s ->
                                                     match uu____3904 with
                                                     | (uu____3916,
                                                        uu____3917, uv) ->
                                                         let uu____3919 =
                                                           FStar_Syntax_Free.uvars
                                                             uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                         FStar_Util.set_union
                                                           s uu____3919) uvs
                                                uu____3887 in
                                            let free_in_some_goal uv =
                                              FStar_Util.set_mem uv uvset in
                                            let uu____3928 = solve' goal w in
                                            FStar_Tactics_Monad.bind
                                              uu____3928
                                              (fun uu____3933 ->
                                                 let uu____3934 =
                                                   FStar_Tactics_Monad.mapM
                                                     (fun uu____3951 ->
                                                        match uu____3951 with
                                                        | (uvt, q, uv) ->
                                                            let uu____3963 =
                                                              FStar_Syntax_Unionfind.find
                                                                uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                            (match uu____3963
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 uu____3968
                                                                 ->
                                                                 FStar_Tactics_Monad.ret
                                                                   ()
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu____3969
                                                                   =
                                                                   uopt &&
                                                                    (free_in_some_goal
                                                                    uv) in
                                                                 if
                                                                   uu____3969
                                                                 then
                                                                   FStar_Tactics_Monad.ret
                                                                    ()
                                                                 else
                                                                   (let uu____3973
                                                                    =
                                                                    let uu____3976
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___684_3979
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___684_3979.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___684_3979.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___684_3979.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    [uu____3976] in
                                                                    FStar_Tactics_Monad.add_goals
                                                                    uu____3973)))
                                                     uvs in
                                                 FStar_Tactics_Monad.bind
                                                   uu____3934
                                                   (fun uu____3983 ->
                                                      proc_guard
                                                        "apply guard" e guard)))))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3680
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____4008 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____4008
    then
      let uu____4015 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4030 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4083 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____4015 with
      | (pre, post) ->
          let post1 =
            let uu____4115 =
              let uu____4126 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____4126] in
            FStar_Syntax_Util.mk_app post uu____4115 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4156 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu____4156
       then
         let uu____4163 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____4163
           (fun post -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStar_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStar_Tactics_Monad.tac
  =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> FStar_Tactics_Monad.ret e
        | x::xs1 ->
            let uu____4240 = f x e in
            FStar_Tactics_Monad.bind uu____4240
              (fun e' -> fold_left f e' xs1)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu____4264 =
          let uu____4267 =
            FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
              (fun ps ->
                 FStar_Tactics_Monad.mlog
                   (fun uu____4274 ->
                      let uu____4275 = FStar_Syntax_Print.term_to_string tm in
                      FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4275)
                   (fun uu____4278 ->
                      let is_unit_t t =
                        let uu____4285 =
                          let uu____4286 = FStar_Syntax_Subst.compress t in
                          uu____4286.FStar_Syntax_Syntax.n in
                        match uu____4285 with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.unit_lid
                            -> true
                        | uu____4290 -> false in
                      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let env1 = FStar_Tactics_Types.goal_env goal in
                           let uu____4296 = __tc env1 tm in
                           FStar_Tactics_Monad.bind uu____4296
                             (fun uu____4319 ->
                                match uu____4319 with
                                | (tm1, t, guard) ->
                                    let uu____4331 =
                                      FStar_Syntax_Util.arrow_formals_comp t in
                                    (match uu____4331 with
                                     | (bs, comp) ->
                                         let uu____4340 = lemma_or_sq comp in
                                         (match uu____4340 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Tactics_Monad.fail
                                                "not a lemma or squashed function"
                                          | FStar_Pervasives_Native.Some
                                              (pre, post) ->
                                              let uu____4359 =
                                                fold_left
                                                  (fun uu____4421 ->
                                                     fun uu____4422 ->
                                                       match (uu____4421,
                                                               uu____4422)
                                                       with
                                                       | ((b, aq),
                                                          (uvs, imps, subst))
                                                           ->
                                                           let b_t =
                                                             FStar_Syntax_Subst.subst
                                                               subst
                                                               b.FStar_Syntax_Syntax.sort in
                                                           let uu____4573 =
                                                             is_unit_t b_t in
                                                           if uu____4573
                                                           then
                                                             FStar_All.pipe_left
                                                               FStar_Tactics_Monad.ret
                                                               (((FStar_Syntax_Util.exp_unit,
                                                                   aq) ::
                                                                 uvs), imps,
                                                                 ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                 :: subst))
                                                           else
                                                             (let uu____4693
                                                                =
                                                                FStar_Tactics_Monad.new_uvar
                                                                  "apply_lemma"
                                                                  env1 b_t in
                                                              FStar_Tactics_Monad.bind
                                                                uu____4693
                                                                (fun
                                                                   uu____4729
                                                                   ->
                                                                   match uu____4729
                                                                   with
                                                                   | 
                                                                   (t1, u) ->
                                                                    FStar_All.pipe_left
                                                                    FStar_Tactics_Monad.ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst)))))
                                                  ([], [], []) bs in
                                              FStar_Tactics_Monad.bind
                                                uu____4359
                                                (fun uu____4917 ->
                                                   match uu____4917 with
                                                   | (uvs, implicits1, subst)
                                                       ->
                                                       let implicits2 =
                                                         FStar_List.rev
                                                           implicits1 in
                                                       let uvs1 =
                                                         FStar_List.rev uvs in
                                                       let pre1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst pre in
                                                       let post1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst post in
                                                       let post_u =
                                                         env1.FStar_TypeChecker_Env.universe_of
                                                           env1 post1 in
                                                       let cmp_func =
                                                         if noinst
                                                         then do_match
                                                         else
                                                           if noinst_lhs
                                                           then
                                                             do_match_on_lhs
                                                           else do_unify in
                                                       let uu____5045 =
                                                         let uu____5048 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal in
                                                         let uu____5049 =
                                                           FStar_Syntax_Util.mk_squash
                                                             post_u post1 in
                                                         cmp_func env1
                                                           uu____5048
                                                           uu____5049 in
                                                       FStar_Tactics_Monad.bind
                                                         uu____5045
                                                         (fun b ->
                                                            if
                                                              Prims.op_Negation
                                                                b
                                                            then
                                                              let uu____5058
                                                                =
                                                                let uu____5063
                                                                  =
                                                                  FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                let uu____5064
                                                                  =
                                                                  FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                FStar_TypeChecker_Err.print_discrepancy
                                                                  (tts env1)
                                                                  uu____5063
                                                                  uu____5064 in
                                                              match uu____5058
                                                              with
                                                              | (post2,
                                                                 goalt) ->
                                                                  let uu____5069
                                                                    =
                                                                    tts env1
                                                                    tm1 in
                                                                  fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu____5069
                                                                    post2
                                                                    goalt
                                                            else
                                                              (let uu____5071
                                                                 =
                                                                 solve' goal
                                                                   FStar_Syntax_Util.exp_unit in
                                                               FStar_Tactics_Monad.bind
                                                                 uu____5071
                                                                 (fun
                                                                    uu____5079
                                                                    ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu____5106
                                                                    =
                                                                    let uu____5109
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____5109 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5106 in
                                                                    FStar_List.existsML
                                                                    (fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu____5146
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5146)
                                                                    goals in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu____5162
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu____5162
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5180)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____5206)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5223
                                                                    -> false) in
                                                                    let uu____5224
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    implicits2
                                                                    (FStar_Tactics_Monad.mapM
                                                                    (fun imp
                                                                    ->
                                                                    let uu____5265
                                                                    = imp in
                                                                    match uu____5265
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____5276
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____5276
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5298)
                                                                    ->
                                                                    let uu____5323
                                                                    =
                                                                    let uu____5324
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd in
                                                                    uu____5324.FStar_Syntax_Syntax.n in
                                                                    (match uu____5323
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____5332)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___810_5352
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___810_5352.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___810_5352.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___810_5352.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___810_5352.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5355
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____5361
                                                                    ->
                                                                    let uu____5362
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____5363
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5362
                                                                    uu____5363)
                                                                    (fun
                                                                    uu____5367
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env1
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                                    let uu____5369
                                                                    =
                                                                    let uu____5372
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5373
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar in
                                                                    let uu____5374
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5373
                                                                    uu____5374
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    proc_guard
                                                                    uu____5372
                                                                    env1
                                                                    g_typ in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5369
                                                                    (fun
                                                                    uu____5379
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    [])))))) in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5224
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
                                                                    let uu____5441
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____5441
                                                                    then
                                                                    let uu____5444
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____5444
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____5458
                                                                    =
                                                                    let uu____5459
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____5459
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____5458)
                                                                    sub_goals1 in
                                                                    let uu____5460
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5460
                                                                    (fun
                                                                    uu____5466
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu____5468
                                                                    =
                                                                    let uu____5471
                                                                    =
                                                                    let uu____5472
                                                                    =
                                                                    let uu____5473
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre_u
                                                                    pre1 in
                                                                    istrivial
                                                                    env1
                                                                    uu____5473 in
                                                                    Prims.op_Negation
                                                                    uu____5472 in
                                                                    if
                                                                    uu____5471
                                                                    then
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    () in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5468
                                                                    (fun
                                                                    uu____5478
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
          focus uu____4267 in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
          uu____4264
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu____5529 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____5529 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu____5564 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu____5564
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5586 = aux e' in
               FStar_Util.map_opt uu____5586
                 (fun uu____5617 ->
                    match uu____5617 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____5643 = aux e in
      FStar_Util.map_opt uu____5643
        (fun uu____5674 ->
           match uu____5674 with
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
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun b1 ->
    fun b2 ->
      fun g ->
        let uu____5749 =
          let uu____5760 = FStar_Tactics_Types.goal_env g in
          split_env b1 uu____5760 in
        match uu____5749 with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu____5800 =
              let uu____5813 = FStar_Syntax_Subst.close_binders bs in
              let uu____5822 = FStar_Syntax_Subst.close bs t in
              (uu____5813, uu____5822) in
            (match uu____5800 with
             | (bs', t') ->
                 let bs'1 =
                   let uu____5866 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu____5873 = FStar_List.tail bs' in uu____5866 ::
                     uu____5873 in
                 let uu____5894 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu____5894 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu____5910 = FStar_List.hd bs'' in
                        FStar_Pervasives_Native.fst uu____5910 in
                      let new_env =
                        let uu____5926 =
                          FStar_List.map FStar_Pervasives_Native.fst bs'' in
                        push_bvs e0 uu____5926 in
                      let uu____5937 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t'' in
                      FStar_Tactics_Monad.bind uu____5937
                        (fun uu____5960 ->
                           match uu____5960 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu____5979 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu____5982 =
                                   FStar_List.map
                                     (fun uu____6003 ->
                                        match uu____6003 with
                                        | (bv, q) ->
                                            let uu____6016 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____6016) bs in
                                 FStar_Syntax_Util.mk_app uu____5979
                                   uu____5982 in
                               let uu____6017 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu____6017
                                 (fun uu____6027 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu____6065 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6073 = h in
           match uu____6073 with
           | (bv, uu____6077) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____6085 ->
                    let uu____6086 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____6087 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6086
                      uu____6087)
                 (fun uu____6090 ->
                    let uu____6091 =
                      let uu____6102 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____6102 in
                    match uu____6091 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____6128 =
                          let uu____6135 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort in
                          destruct_eq uu____6135 in
                        (match uu____6128 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____6144 =
                               let uu____6145 = FStar_Syntax_Subst.compress x in
                               uu____6145.FStar_Syntax_Syntax.n in
                             (match uu____6144 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let t = FStar_Tactics_Types.goal_type goal in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs in
                                  let uu____6172 =
                                    let uu____6177 =
                                      FStar_Syntax_Subst.close_binders bs in
                                    let uu____6178 =
                                      FStar_Syntax_Subst.close bs t in
                                    (uu____6177, uu____6178) in
                                  (match uu____6172 with
                                   | (bs', t') ->
                                       let uu____6183 =
                                         let uu____6188 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs' in
                                         let uu____6189 =
                                           FStar_Syntax_Subst.subst s t in
                                         (uu____6188, uu____6189) in
                                       (match uu____6183 with
                                        | (bs'1, t'1) ->
                                            let uu____6194 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1 in
                                            (match uu____6194 with
                                             | (bs'', t'') ->
                                                 let new_env =
                                                   let uu____6204 =
                                                     let uu____6207 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs'' in
                                                     bv1 :: uu____6207 in
                                                   push_bvs e0 uu____6204 in
                                                 let uu____6218 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t'' in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6218
                                                   (fun uu____6235 ->
                                                      match uu____6235 with
                                                      | (uvt, uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label in
                                                          let sol =
                                                            let uu____6248 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None in
                                                            let uu____6251 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6272
                                                                   ->
                                                                   match uu____6272
                                                                   with
                                                                   | 
                                                                   (bv2,
                                                                    uu____6280)
                                                                    ->
                                                                    let uu____6285
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6285)
                                                                bs in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6248
                                                              uu____6251 in
                                                          let uu____6286 =
                                                            set_solution goal
                                                              sol in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6286
                                                            (fun uu____6290
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6291 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6292 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis"))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____6065
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu____6317 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6339 = b in
             match uu____6339 with
             | (bv, q) ->
                 let bv' =
                   let uu____6355 =
                     let uu___932_6356 = bv in
                     let uu____6357 =
                       let uu____6358 =
                         let uu____6363 =
                           FStar_Ident.range_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         (s, uu____6363) in
                       FStar_Ident.mk_ident uu____6358 in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6357;
                       FStar_Syntax_Syntax.index =
                         (uu___932_6356.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___932_6356.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____6355 in
                 let uu____6364 = subst_goal bv bv' goal in
                 FStar_Tactics_Monad.bind uu____6364
                   (fun uu___4_6386 ->
                      match uu___4_6386 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                          let uu____6417 =
                            FStar_Tactics_Monad.replace_cur goal1 in
                          FStar_Tactics_Monad.bind uu____6417
                            (fun uu____6427 ->
                               FStar_Tactics_Monad.ret (bv'1, q)))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6317
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu____6461 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6470 = b in
           match uu____6470 with
           | (bv, uu____6474) ->
               let uu____6479 =
                 let uu____6490 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____6490 in
               (match uu____6479 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____6516 = FStar_Syntax_Util.type_u () in
                    (match uu____6516 with
                     | (ty, u) ->
                         let uu____6525 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty in
                         FStar_Tactics_Monad.bind uu____6525
                           (fun uu____6543 ->
                              match uu____6543 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___959_6553 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___959_6553.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___959_6553.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____6557 =
                                      let uu____6558 =
                                        let uu____6565 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____6565) in
                                      FStar_Syntax_Syntax.NT uu____6558 in
                                    [uu____6557] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___964_6577 = b1 in
                                         let uu____6578 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___964_6577.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___964_6577.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6578
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6585 ->
                                       let new_goal =
                                         let uu____6587 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____6588 =
                                           let uu____6589 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____6589 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6587 uu____6588 in
                                       let uu____6590 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal] in
                                       FStar_Tactics_Monad.bind uu____6590
                                         (fun uu____6595 ->
                                            let uu____6596 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____6596)))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6461
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu____6619 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6628 = b in
             match uu____6628 with
             | (bv, uu____6632) ->
                 let uu____6637 =
                   let uu____6648 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____6648 in
                 (match uu____6637 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____6677 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6677 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___985_6682 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___985_6682.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___985_6682.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____6684 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      FStar_Tactics_Monad.replace_cur uu____6684)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____6619
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6695 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6701 =
           let uu____6708 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6708 in
         match uu____6701 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____6724 =
                 let uu____6727 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____6727 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6724 in
             let uu____6742 = FStar_Tactics_Monad.new_uvar "revert" env' typ' in
             FStar_Tactics_Monad.bind uu____6742
               (fun uu____6757 ->
                  match uu____6757 with
                  | (r, u_r) ->
                      let uu____6766 =
                        let uu____6769 =
                          let uu____6770 =
                            let uu____6771 =
                              let uu____6780 =
                                FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu____6780 in
                            [uu____6771] in
                          let uu____6797 =
                            let uu____6798 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____6798.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu____6770
                            uu____6797 in
                        set_solution goal uu____6769 in
                      FStar_Tactics_Monad.bind uu____6766
                        (fun uu____6803 ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label in
                           FStar_Tactics_Monad.replace_cur g)))
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____6815 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6815
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____6835 ->
              let uu____6836 = FStar_Syntax_Print.binder_to_string b in
              let uu____6837 =
                let uu____6838 =
                  let uu____6839 =
                    let uu____6848 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____6848 in
                  FStar_All.pipe_right uu____6839 FStar_List.length in
                FStar_All.pipe_right uu____6838 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6836 uu____6837)
           (fun uu____6865 ->
              let uu____6866 =
                let uu____6877 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____6877 in
              match uu____6866 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____6921 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____6921
                        then
                          let uu____6924 =
                            let uu____6925 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6925 in
                          FStar_Tactics_Monad.fail uu____6924
                        else check bvs2 in
                  let uu____6927 =
                    let uu____6928 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____6928 in
                  if uu____6927
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____6932 = check bvs in
                     FStar_Tactics_Monad.bind uu____6932
                       (fun uu____6938 ->
                          let env' = push_bvs e' bvs in
                          let uu____6940 =
                            let uu____6947 =
                              FStar_Tactics_Types.goal_type goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____6947 in
                          FStar_Tactics_Monad.bind uu____6940
                            (fun uu____6956 ->
                               match uu____6956 with
                               | (ut, uvar_ut) ->
                                   let uu____6965 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu____6965
                                     (fun uu____6970 ->
                                        let uu____6971 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____6971))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6978 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6984 =
           let uu____6991 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6991 in
         match uu____6984 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____6999) ->
             let uu____7004 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____7004)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7021 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7021 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7039 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7039 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (_trefl :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun l ->
    fun r ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7058 =
             let uu____7061 = FStar_Tactics_Types.goal_env g in
             do_unify uu____7061 l r in
           FStar_Tactics_Monad.bind uu____7058
             (fun b ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____7068 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7068 l in
                   let r1 =
                     let uu____7070 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7070 r in
                   let uu____7071 =
                     let uu____7074 = FStar_Tactics_Types.goal_env g in
                     do_unify uu____7074 l1 r1 in
                   FStar_Tactics_Monad.bind uu____7071
                     (fun b1 ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____7080 =
                             let uu____7085 =
                               let uu____7090 =
                                 FStar_Tactics_Types.goal_env g in
                               tts uu____7090 in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____7085 l1 r1 in
                           match uu____7080 with
                           | (ls, rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7101 ->
    let uu____7104 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7112 =
             let uu____7119 =
               let uu____7120 = FStar_Tactics_Types.goal_env g in
               let uu____7121 = FStar_Tactics_Types.goal_type g in
               whnf uu____7120 uu____7121 in
             destruct_eq uu____7119 in
           match uu____7112 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl l r
           | FStar_Pervasives_Native.None ->
               let uu____7134 =
                 let uu____7135 = FStar_Tactics_Types.goal_env g in
                 let uu____7136 = FStar_Tactics_Types.goal_type g in
                 tts uu____7135 uu____7136 in
               fail1 "not an equality (%s)" uu____7134) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7104
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7147 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu____7155 =
           let uu____7162 = FStar_Tactics_Types.goal_type g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu____7162 in
         FStar_Tactics_Monad.bind uu____7155
           (fun uu____7171 ->
              match uu____7171 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1071_7181 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1071_7181.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1071_7181.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1071_7181.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1071_7181.FStar_Tactics_Types.label)
                    } in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7185 ->
                       let t_eq =
                         let uu____7187 =
                           let uu____7188 = FStar_Tactics_Types.goal_type g in
                           env1.FStar_TypeChecker_Env.universe_of env1
                             uu____7188 in
                         let uu____7189 = FStar_Tactics_Types.goal_type g in
                         let uu____7190 = FStar_Tactics_Types.goal_witness g in
                         FStar_Syntax_Util.mk_eq2 uu____7187 uu____7189 u
                           uu____7190 in
                       let uu____7191 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env1 t_eq in
                       FStar_Tactics_Monad.bind uu____7191
                         (fun uu____7196 ->
                            let uu____7197 =
                              FStar_Tactics_Monad.add_goals [g'] in
                            FStar_Tactics_Monad.bind uu____7197
                              (fun uu____7201 -> FStar_Tactics_Monad.ret ())))))
let longest_prefix :
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
              let uu____7324 = f x y in
              if uu____7324 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7344 -> (acc, l11, l21) in
        let uu____7359 = aux [] l1 l2 in
        match uu____7359 with | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs bs f =
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f in
      let uu____7464 = FStar_Tactics_Types.get_phi g1 in
      match uu____7464 with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7470 = FStar_Tactics_Types.get_phi g2 in
          (match uu____7470 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____7482 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____7482 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____7513 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs uu____7513 phi1 in
                    let t2 =
                      let uu____7523 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs uu____7523 phi2 in
                    let uu____7532 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu____7532
                      (fun uu____7537 ->
                         let uu____7538 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu____7538
                           (fun uu____7545 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1123_7550 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____7551 =
                                  FStar_Util.smap_create (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1123_7550.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1123_7550.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1123_7550.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1123_7550.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____7551;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1123_7550.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1123_7550.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1123_7550.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1123_7550.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1123_7550.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1123_7550.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1123_7550.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1123_7550.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1123_7550.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1123_7550.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1123_7550.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1123_7550.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1123_7550.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1123_7550.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1123_7550.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1123_7550.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1123_7550.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1123_7550.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1123_7550.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1123_7550.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1123_7550.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1123_7550.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1123_7550.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1123_7550.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1123_7550.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1123_7550.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1123_7550.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1123_7550.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1123_7550.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1123_7550.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1123_7550.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1123_7550.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1123_7550.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1123_7550.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1123_7550.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1123_7550.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1123_7550.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1123_7550.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1123_7550.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1123_7550.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1123_7550.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____7554 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu____7554
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____7563 ->
                                        let uu____7564 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu____7565 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu____7566 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____7564 uu____7565 uu____7566)
                                     (fun uu____7568 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7575 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____7591 =
               FStar_Tactics_Monad.set
                 (let uu___1138_7596 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1138_7596.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1138_7596.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1138_7596.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1138_7596.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1138_7596.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1138_7596.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1138_7596.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1138_7596.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1138_7596.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1138_7596.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1138_7596.FStar_Tactics_Types.local_state)
                  }) in
             FStar_Tactics_Monad.bind uu____7591
               (fun uu____7599 ->
                  let uu____7600 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu____7600
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____7605 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu____7617 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu____7630 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____7630);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1149_7637 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1149_7637.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1149_7637.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1149_7637.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1149_7637.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____7617
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____7649 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____7662 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu____7668 =
           (FStar_Options.lax ()) ||
             (let uu____7670 = FStar_Tactics_Types.goal_env g in
              uu____7670.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu____7668)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu____7685 =
        FStar_Tactics_Monad.mlog
          (fun uu____7690 ->
             let uu____7691 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____7691)
          (fun uu____7693 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu____7699 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____7699 ty in
                  let uu____7700 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu____7700
                    (fun uu____7719 ->
                       match uu____7719 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____7733 ->
                                let uu____7734 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____7734)
                             (fun uu____7736 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____7739 ->
                                     let uu____7740 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____7740)
                                  (fun uu____7743 ->
                                     let uu____7744 =
                                       proc_guard "unquote" env1 guard in
                                     FStar_Tactics_Monad.bind uu____7744
                                       (fun uu____7748 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____7685
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      let uu____7771 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____7777 =
              let uu____7784 =
                let uu____7785 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7785 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu____7784 in
            FStar_Tactics_Monad.bind uu____7777
              (fun uu____7801 ->
                 match uu____7801 with
                 | (typ, uvar_typ) -> FStar_Tactics_Monad.ret typ) in
      FStar_Tactics_Monad.bind uu____7771
        (fun typ ->
           let uu____7813 = FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ in
           FStar_Tactics_Monad.bind uu____7813
             (fun uu____7827 ->
                match uu____7827 with
                | (t, uvar_t) -> FStar_Tactics_Monad.ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____7845 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7864 -> g.FStar_Tactics_Types.opts
             | uu____7867 -> FStar_Options.peek () in
           let uu____7870 = FStar_Syntax_Util.head_and_args t in
           match uu____7870 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____7890);
                FStar_Syntax_Syntax.pos = uu____7891;
                FStar_Syntax_Syntax.vars = uu____7892;_},
              uu____7893) ->
               let env2 =
                 let uu___1203_7935 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1203_7935.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1203_7935.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1203_7935.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1203_7935.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1203_7935.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1203_7935.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1203_7935.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1203_7935.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1203_7935.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1203_7935.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1203_7935.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1203_7935.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1203_7935.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1203_7935.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1203_7935.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1203_7935.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1203_7935.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1203_7935.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1203_7935.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1203_7935.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1203_7935.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1203_7935.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1203_7935.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1203_7935.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1203_7935.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1203_7935.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1203_7935.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1203_7935.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1203_7935.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1203_7935.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1203_7935.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1203_7935.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1203_7935.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1203_7935.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1203_7935.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1203_7935.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1203_7935.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1203_7935.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1203_7935.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1203_7935.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1203_7935.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1203_7935.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1203_7935.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1203_7935.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1203_7935.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1203_7935.FStar_TypeChecker_Env.enable_defer_to_tac)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let uu____7937 = let uu____7940 = bnorm_goal g in [uu____7940] in
               FStar_Tactics_Monad.add_goals uu____7937
           | uu____7941 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____7845
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu____7990 = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu____7990
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu____8001 = trytac comp in
      FStar_Tactics_Monad.bind uu____8001
        (fun uu___5_8009 ->
           match uu___5_8009 with
           | FStar_Pervasives_Native.Some (true) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (match_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8035 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8041 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8041
                 (fun uu____8061 ->
                    match uu____8061 with
                    | (t11, ty1, g1) ->
                        let uu____8073 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8073
                          (fun uu____8093 ->
                             match uu____8093 with
                             | (t21, ty2, g2) ->
                                 let uu____8105 =
                                   proc_guard "match_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8105
                                   (fun uu____8110 ->
                                      let uu____8111 =
                                        proc_guard "match_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8111
                                        (fun uu____8117 ->
                                           let uu____8118 =
                                             do_match e ty1 ty2 in
                                           let uu____8121 =
                                             do_match e t11 t21 in
                                           tac_and uu____8118 uu____8121))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "match_env")
          uu____8035
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8147 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8153 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8153
                 (fun uu____8173 ->
                    match uu____8173 with
                    | (t11, ty1, g1) ->
                        let uu____8185 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8185
                          (fun uu____8205 ->
                             match uu____8205 with
                             | (t21, ty2, g2) ->
                                 let uu____8217 =
                                   proc_guard "unify_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8217
                                   (fun uu____8222 ->
                                      let uu____8223 =
                                        proc_guard "unify_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8223
                                        (fun uu____8229 ->
                                           let uu____8230 =
                                             do_unify e ty1 ty2 in
                                           let uu____8233 =
                                             do_unify e t11 t21 in
                                           tac_and uu____8230 uu____8233))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____8147
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8266 ->
             let uu____8267 = FStar_Options.unsafe_tactic_exec () in
             if uu____8267
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input) in
               FStar_Tactics_Monad.ret s
             else
               FStar_Tactics_Monad.fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let (fresh_bv_named :
  Prims.string ->
    FStar_Reflection_Data.typ ->
      FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
        (fun uu____8288 ->
           let uu____8289 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu____8289)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu____8299 =
      FStar_Tactics_Monad.mlog
        (fun uu____8304 ->
           let uu____8305 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____8305)
        (fun uu____8307 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu____8311 =
                  let uu____8320 = FStar_Tactics_Types.goal_env g in
                  __tc uu____8320 ty in
                FStar_Tactics_Monad.bind uu____8311
                  (fun uu____8332 ->
                     match uu____8332 with
                     | (ty1, uu____8342, guard) ->
                         let uu____8344 =
                           let uu____8347 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____8347 guard in
                         FStar_Tactics_Monad.bind uu____8344
                           (fun uu____8350 ->
                              let uu____8351 =
                                let uu____8354 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____8355 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____8354 uu____8355 ty1 in
                              FStar_Tactics_Monad.bind uu____8351
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____8361 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8361
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____8367 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____8368 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____8367 uu____8368 in
                                      let nty =
                                        let uu____8370 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____8370 ty1 in
                                      let uu____8371 =
                                        let uu____8374 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____8374 ng nty in
                                      FStar_Tactics_Monad.bind uu____8371
                                        (fun b ->
                                           if b
                                           then
                                             let uu____8380 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8380
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8299
let failwhen :
  'a .
    Prims.bool ->
      Prims.string ->
        (unit -> 'a FStar_Tactics_Monad.tac) -> 'a FStar_Tactics_Monad.tac
  =
  fun b ->
    fun msg -> fun k -> if b then FStar_Tactics_Monad.fail msg else k ()
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu____8443 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____8461 =
             let uu____8470 = FStar_Tactics_Types.goal_env g in
             __tc uu____8470 s_tm in
           FStar_Tactics_Monad.bind uu____8461
             (fun uu____8488 ->
                match uu____8488 with
                | (s_tm1, s_ty, guard) ->
                    let uu____8506 =
                      let uu____8509 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____8509 guard in
                    FStar_Tactics_Monad.bind uu____8506
                      (fun uu____8522 ->
                         let s_ty1 =
                           let uu____8524 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____8524
                             s_ty in
                         let uu____8525 =
                           let uu____8540 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args' uu____8540 in
                         match uu____8525 with
                         | (h, args) ->
                             let uu____8571 =
                               let uu____8578 =
                                 let uu____8579 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____8579.FStar_Syntax_Syntax.n in
                               match uu____8578 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____8594;
                                      FStar_Syntax_Syntax.vars = uu____8595;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____8605 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu____8571
                               (fun uu____8625 ->
                                  match uu____8625 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____8641 =
                                        let uu____8644 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____8644 t_lid in
                                      (match uu____8641 with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Tactics_Monad.fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid, t_us, t_ps, t_ty, mut,
                                                 c_lids)
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr in
                                                let uu____8683 =
                                                  erasable &&
                                                    (let uu____8685 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu____8685) in
                                                failwhen uu____8683
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____8693 ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____8705 ->
                                                          let uu____8706 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu____8706
                                                          with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu____8721
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu____8749
                                                                    =
                                                                    let uu____8752
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____8752
                                                                    c_lid in
                                                                    match uu____8749
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
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
                                                                    uu____8825
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____8830
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____8830
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____8853
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____8853
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____8872
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu____8895
                                                                    =
                                                                    let uu____8900
                                                                    =
                                                                    let uu____8901
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu____8901 in
                                                                    let uu____8902
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu____8900,
                                                                    uu____8902) in
                                                                    FStar_Ident.mk_ident
                                                                    uu____8895 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1345_8905
                                                                    = bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1345_8905.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1345_8905.FStar_Syntax_Syntax.sort)
                                                                    }) in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____8931
                                                                    ->
                                                                    match uu____8931
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    let uu____8950
                                                                    =
                                                                    rename_bv
                                                                    bv in
                                                                    (uu____8950,
                                                                    aq)) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____8975
                                                                    ->
                                                                    fun
                                                                    uu____8976
                                                                    ->
                                                                    match 
                                                                    (uu____8975,
                                                                    uu____8976)
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9002),
                                                                    (bv',
                                                                    uu____9004))
                                                                    ->
                                                                    let uu____9025
                                                                    =
                                                                    let uu____9032
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu____9032) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9025)
                                                                    bs bs' in
                                                                    let uu____9037
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu____9046
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu____9037,
                                                                    uu____9046) in
                                                                    (match uu____8872
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu____9093
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu____9093
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu____9166
                                                                    =
                                                                    let uu____9167
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu____9167 in
                                                                    failwhen
                                                                    uu____9166
                                                                    "not total?"
                                                                    (fun
                                                                    uu____9184
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
                                                                    uu___6_9200
                                                                    =
                                                                    match uu___6_9200
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9203)
                                                                    -> true
                                                                    | 
                                                                    uu____9204
                                                                    -> false in
                                                                    let uu____9207
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____9207
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
                                                                    uu____9342
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9404
                                                                    ->
                                                                    match uu____9404
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9424),
                                                                    (t,
                                                                    uu____9426))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9494
                                                                    ->
                                                                    match uu____9494
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9520),
                                                                    (t,
                                                                    uu____9522))
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
                                                                    uu____9577
                                                                    ->
                                                                    match uu____9577
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs3 in
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
                                                                    let env1
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1
                                                                    s_ty1 in
                                                                    let uu____9627
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1404_9650
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1404_9650.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat in
                                                                    match uu____9627
                                                                    with
                                                                    | 
                                                                    (uu____9663,
                                                                    uu____9664,
                                                                    uu____9665,
                                                                    uu____9666,
                                                                    pat_t,
                                                                    uu____9668,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____9680
                                                                    =
                                                                    let uu____9681
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____9681 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____9680 in
                                                                    let cod1
                                                                    =
                                                                    let uu____9685
                                                                    =
                                                                    let uu____9694
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____9694] in
                                                                    let uu____9713
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9685
                                                                    uu____9713 in
                                                                    let nty =
                                                                    let uu____9719
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____9719 in
                                                                    let uu____9722
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9722
                                                                    (fun
                                                                    uu____9751
                                                                    ->
                                                                    match uu____9751
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env1 uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3 in
                                                                    let brt1
                                                                    =
                                                                    let uu____9777
                                                                    =
                                                                    let uu____9788
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____9788] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____9777 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____9824
                                                                    =
                                                                    let uu____9835
                                                                    =
                                                                    let uu____9840
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu____9840) in
                                                                    (g', br,
                                                                    uu____9835) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____9824)))))))
                                                                    | 
                                                                    uu____9861
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu____8721
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu____9910
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs in
                                                                   match uu____9910
                                                                   with
                                                                   | 
                                                                   (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu____9983
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9983
                                                                    (fun
                                                                    uu____9994
                                                                    ->
                                                                    let uu____9995
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9995
                                                                    (fun
                                                                    uu____10005
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____10012 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8443
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10057::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10085 = init xs in x :: uu____10085
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu____10097 =
      let uu____10100 = top_env () in
      FStar_Tactics_Monad.bind uu____10100
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.un_uinst t1 in
           let t3 = FStar_Syntax_Util.unlazy_emb t2 in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4, uu____10116) -> inspect t4
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_app (hd, []) ->
               failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app (hd, args) ->
               let uu____10181 = last args in
               (match uu____10181 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu____10211 =
                      let uu____10212 =
                        let uu____10217 =
                          let uu____10218 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu____10218
                            t3.FStar_Syntax_Syntax.pos in
                        (uu____10217, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu____10212 in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10211)
           | FStar_Syntax_Syntax.Tm_abs ([], uu____10229, uu____10230) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
               let uu____10282 = FStar_Syntax_Subst.open_term bs t4 in
               (match uu____10282 with
                | (bs1, t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10323 =
                           let uu____10324 =
                             let uu____10329 = FStar_Syntax_Util.abs bs2 t5 k in
                             (b, uu____10329) in
                           FStar_Reflection_Data.Tv_Abs uu____10324 in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10323))
           | FStar_Syntax_Syntax.Tm_type uu____10332 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10356 ->
               let uu____10371 = FStar_Syntax_Util.arrow_one t3 in
               (match uu____10371 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____10401 = FStar_Syntax_Subst.open_term [b] t4 in
               (match uu____10401 with
                | (b', t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____10454 -> failwith "impossible" in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____10466 =
                 let uu____10467 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu____10467 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10466
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu____10488 =
                 let uu____10489 =
                   let uu____10494 =
                     let uu____10495 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu____10495 in
                   (uu____10494, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu____10489 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10488
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10529 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu____10534 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu____10534 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____10587 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders" in
                           FStar_All.pipe_left FStar_Tactics_Monad.ret
                             (FStar_Reflection_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (FStar_Pervasives_Native.fst b1),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10623 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____10627 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu____10627 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____10647 ->
                                     FStar_Tactics_Monad.ret
                                       FStar_Reflection_Data.Tv_Unknown
                                 | FStar_Util.Inl bv1 ->
                                     FStar_All.pipe_left
                                       FStar_Tactics_Monad.ret
                                       (FStar_Reflection_Data.Tv_Let
                                          (true,
                                            (lb1.FStar_Syntax_Syntax.lbattrs),
                                            bv1,
                                            (lb1.FStar_Syntax_Syntax.lbdef),
                                            t22)))
                            | uu____10653 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____10707 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu____10707
                 | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                     let uu____10726 =
                       let uu____10737 =
                         FStar_List.map
                           (fun uu____10758 ->
                              match uu____10758 with
                              | (p1, b) ->
                                  let uu____10775 = inspect_pat p1 in
                                  (uu____10775, b)) ps in
                       (fv, uu____10737) in
                     FStar_Reflection_Data.Pat_Cons uu____10726
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_List.map
                   (fun uu___7_10869 ->
                      match uu___7_10869 with
                      | (pat, uu____10891, t5) ->
                          let uu____10909 = inspect_pat pat in
                          (uu____10909, t5)) brs1 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____10918 ->
               ((let uu____10920 =
                   let uu____10925 =
                     let uu____10926 = FStar_Syntax_Print.tag_of_term t3 in
                     let uu____10927 = term_to_string e t3 in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____10926 uu____10927 in
                   (FStar_Errors.Warning_CantInspect, uu____10925) in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____10920);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu____10097
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10940 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10940
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10944 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10944
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10948 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10948
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____10955 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10955
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____10980 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10980
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____10997 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10997
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____11016 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11016
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11020 =
          let uu____11021 =
            let uu____11022 = FStar_Reflection_Basic.pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____11022 in
          FStar_Syntax_Syntax.mk uu____11021 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11020
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____11027 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11027
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11039 =
          let uu____11040 =
            let uu____11041 =
              let uu____11054 =
                let uu____11057 =
                  let uu____11058 = FStar_Syntax_Syntax.mk_binder bv in
                  [uu____11058] in
                FStar_Syntax_Subst.close uu____11057 t2 in
              ((false, [lb]), uu____11054) in
            FStar_Syntax_Syntax.Tm_let uu____11041 in
          FStar_Syntax_Syntax.mk uu____11040 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11039
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11098 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____11098 with
         | (lbs, body) ->
             let uu____11113 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Range.dummyRange in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11113)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11147 =
                let uu____11148 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____11148 in
              FStar_All.pipe_left wrap uu____11147
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____11163 =
                let uu____11164 =
                  let uu____11177 =
                    FStar_List.map
                      (fun uu____11198 ->
                         match uu____11198 with
                         | (p1, b) ->
                             let uu____11209 = pack_pat p1 in
                             (uu____11209, b)) ps in
                  (fv, uu____11177) in
                FStar_Syntax_Syntax.Pat_cons uu____11164 in
              FStar_All.pipe_left wrap uu____11163
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___8_11255 ->
               match uu___8_11255 with
               | (pat, t1) ->
                   let uu____11272 = pack_pat pat in
                   (uu____11272, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____11320 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11320
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____11348 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11348
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____11394 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11394
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____11433 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11433
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu____11450 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu____11456 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____11456 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____11450
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____11485 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1709_11492 = ps in
                 let uu____11493 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1709_11492.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1709_11492.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1709_11492.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1709_11492.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1709_11492.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1709_11492.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1709_11492.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1709_11492.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1709_11492.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1709_11492.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1709_11492.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____11493
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____11485
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env1 ->
    fun typ ->
      let uu____11518 =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env1 typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
      match uu____11518 with
      | (u, ctx_uvars, g_u) ->
          let uu____11550 = FStar_List.hd ctx_uvars in
          (match uu____11550 with
           | (ctx_uvar, uu____11564) ->
               let g =
                 let uu____11566 = FStar_Options.peek () in
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar uu____11566 false
                   "" in
               (g, g_u))
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu____11572 = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu____11572 with
    | (env2, uu____11580) ->
        let env3 =
          let uu___1726_11586 = env2 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1726_11586.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1726_11586.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1726_11586.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1726_11586.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1726_11586.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1726_11586.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1726_11586.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1726_11586.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1726_11586.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1726_11586.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1726_11586.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1726_11586.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1726_11586.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1726_11586.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1726_11586.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1726_11586.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1726_11586.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1726_11586.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1726_11586.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1726_11586.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1726_11586.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1726_11586.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1726_11586.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1726_11586.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1726_11586.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1726_11586.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1726_11586.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1726_11586.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1726_11586.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1726_11586.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1726_11586.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1726_11586.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1726_11586.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1726_11586.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1726_11586.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1726_11586.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1726_11586.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1726_11586.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1726_11586.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1726_11586.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1726_11586.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1726_11586.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1726_11586.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1726_11586.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1726_11586.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1726_11586.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env4 =
          let uu___1729_11588 = env3 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1729_11588.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1729_11588.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1729_11588.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1729_11588.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1729_11588.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1729_11588.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1729_11588.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1729_11588.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1729_11588.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1729_11588.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1729_11588.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1729_11588.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1729_11588.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1729_11588.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1729_11588.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1729_11588.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1729_11588.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1729_11588.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1729_11588.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1729_11588.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1729_11588.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1729_11588.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1729_11588.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1729_11588.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1729_11588.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1729_11588.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1729_11588.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1729_11588.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1729_11588.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1729_11588.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1729_11588.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1729_11588.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1729_11588.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1729_11588.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1729_11588.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1729_11588.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1729_11588.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1729_11588.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1729_11588.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1729_11588.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1729_11588.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1729_11588.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1729_11588.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1729_11588.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1729_11588.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1729_11588.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        env4
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng ->
    fun env1 ->
      fun goals ->
        fun imps ->
          let env2 = tac_env env1 in
          let ps =
            let uu____11619 =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu____11620 = FStar_Util.psmap_empty () in
            {
              FStar_Tactics_Types.main_context = env2;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump =
                FStar_Tactics_Printing.do_dump_proofstate;
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu____11619;
              FStar_Tactics_Types.local_state = uu____11620
            } in
          ps
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun typ ->
        let env2 = tac_env env1 in
        let uu____11643 = goal_of_goal_ty env2 typ in
        match uu____11643 with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu____11655 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____11655)
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env1 ->
    fun i ->
      let uu____11666 = FStar_Options.peek () in
      FStar_Tactics_Types.mk_goal
        (let uu___1748_11669 = env1 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1748_11669.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1748_11669.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1748_11669.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1748_11669.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1748_11669.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1748_11669.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1748_11669.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1748_11669.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1748_11669.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1748_11669.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1748_11669.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1748_11669.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1748_11669.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1748_11669.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1748_11669.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1748_11669.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1748_11669.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___1748_11669.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___1748_11669.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___1748_11669.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1748_11669.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1748_11669.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1748_11669.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1748_11669.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1748_11669.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1748_11669.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1748_11669.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1748_11669.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1748_11669.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1748_11669.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1748_11669.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1748_11669.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1748_11669.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1748_11669.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1748_11669.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1748_11669.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1748_11669.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1748_11669.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1748_11669.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1748_11669.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1748_11669.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1748_11669.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1748_11669.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1748_11669.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1748_11669.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1748_11669.FStar_TypeChecker_Env.enable_defer_to_tac)
         }) i.FStar_TypeChecker_Common.imp_uvar uu____11666 false
        i.FStar_TypeChecker_Common.imp_reason
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun imps ->
        let env2 = tac_env env1 in
        let goals = FStar_List.map (goal_of_implicit env2) imps in
        let w =
          let uu____11694 = FStar_List.hd goals in
          FStar_Tactics_Types.goal_witness uu____11694 in
        let ps =
          let uu____11696 =
            FStar_TypeChecker_Env.debug env2
              (FStar_Options.Other "TacVerbose") in
          let uu____11697 = FStar_Util.psmap_empty () in
          {
            FStar_Tactics_Types.main_context = env2;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps ->
                 fun msg -> FStar_Tactics_Printing.do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____11696;
            FStar_Tactics_Types.local_state = uu____11697
          } in
        (ps, w)