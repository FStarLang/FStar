open Prims
let (dbg_Tac : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "Tac"
let solve : 'a . 'a -> 'a = fun ev -> ev
let embed :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Compiler_Range_Type.range ->
        'a ->
          FStar_Syntax_Embeddings_Base.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu___1 = FStar_Syntax_Embeddings_Base.embed uu___ x in
          uu___1 r FStar_Pervasives_Native.None norm_cb
let unembed :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings_Base.norm_cb ->
          'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun a1 ->
      fun norm_cb -> FStar_Syntax_Embeddings_Base.unembed uu___ a1 norm_cb
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  fun uu___ ->
    let step_from_native_step s =
      {
        FStar_TypeChecker_Primops_Base.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Primops_Base.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Primops_Base.univ_arity = Prims.int_zero;
        FStar_TypeChecker_Primops_Base.auto_reflect =
          (FStar_Pervasives_Native.Some
             (s.FStar_Tactics_Native.arity - Prims.int_one));
        FStar_TypeChecker_Primops_Base.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Primops_Base.requires_binder_substitution = false;
        FStar_TypeChecker_Primops_Base.renorm_after = false;
        FStar_TypeChecker_Primops_Base.interpretation =
          (s.FStar_Tactics_Native.tactic);
        FStar_TypeChecker_Primops_Base.interpretation_nbe =
          (fun _cb ->
             fun _us ->
               FStar_TypeChecker_NBETerm.dummy_interp
                 s.FStar_Tactics_Native.name)
      } in
    let uu___1 = FStar_Tactics_Native.list_all () in
    FStar_Compiler_List.map step_from_native_step uu___1
let (__primitive_steps_ref :
  FStar_TypeChecker_Primops_Base.primitive_step Prims.list
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref []
let (primitive_steps :
  unit -> FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  fun uu___ ->
    let uu___1 = native_tactics_steps () in
    let uu___2 = FStar_Compiler_Effect.op_Bang __primitive_steps_ref in
    FStar_Compiler_List.op_At uu___1 uu___2
let (register_tactic_primitive_step :
  FStar_TypeChecker_Primops_Base.primitive_step -> unit) =
  fun s ->
    let uu___ =
      let uu___1 = FStar_Compiler_Effect.op_Bang __primitive_steps_ref in s
        :: uu___1 in
    FStar_Compiler_Effect.op_Colon_Equals __primitive_steps_ref uu___
let rec (t_head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_app uu___1 ->
        let uu___2 = FStar_Syntax_Util.head_and_args_full t in
        (match uu___2 with
         | (h, args) ->
             let h1 = FStar_Syntax_Util.unmeta h in
             let uu___3 =
               let uu___4 = FStar_Syntax_Subst.compress h1 in
               uu___4.FStar_Syntax_Syntax.n in
             (match uu___3 with
              | FStar_Syntax_Syntax.Tm_uinst uu___4 -> t
              | FStar_Syntax_Syntax.Tm_fvar uu___4 -> t
              | FStar_Syntax_Syntax.Tm_bvar uu___4 -> t
              | FStar_Syntax_Syntax.Tm_name uu___4 -> t
              | FStar_Syntax_Syntax.Tm_constant uu___4 -> t
              | uu___4 -> t_head_of h1))
    | FStar_Syntax_Syntax.Tm_match
        { FStar_Syntax_Syntax.scrutinee = t1;
          FStar_Syntax_Syntax.ret_opt = uu___1;
          FStar_Syntax_Syntax.brs = uu___2;
          FStar_Syntax_Syntax.rc_opt1 = uu___3;_}
        -> t_head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed
        { FStar_Syntax_Syntax.tm = t1; FStar_Syntax_Syntax.asc = uu___1;
          FStar_Syntax_Syntax.eff_opt = uu___2;_}
        -> t_head_of t1
    | FStar_Syntax_Syntax.Tm_meta
        { FStar_Syntax_Syntax.tm2 = t1; FStar_Syntax_Syntax.meta = uu___1;_}
        -> t_head_of t1
    | uu___1 -> t
let unembed_tactic_0 :
  'b .
    'b FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings_Base.norm_cb -> 'b FStar_Tactics_Monad.tac
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun eb ->
           fun embedded_tac_b ->
             fun ncb ->
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                    () () (Obj.magic FStar_Tactics_Monad.get)
                    (fun uu___ ->
                       (fun proof_state ->
                          let proof_state = Obj.magic proof_state in
                          let rng = embedded_tac_b.FStar_Syntax_Syntax.pos in
                          let embedded_tac_b1 =
                            FStar_Syntax_Util.mk_reify embedded_tac_b
                              (FStar_Pervasives_Native.Some
                                 FStar_Parser_Const.effect_TAC_lid) in
                          let tm =
                            let uu___ =
                              let uu___1 =
                                let uu___2 =
                                  embed FStar_Tactics_Embedding.e_proofstate
                                    rng proof_state ncb in
                                FStar_Syntax_Syntax.as_arg uu___2 in
                              [uu___1] in
                            FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1
                              uu___ rng in
                          let steps =
                            [FStar_TypeChecker_Env.Weak;
                            FStar_TypeChecker_Env.Reify;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                            FStar_TypeChecker_Env.UnfoldTac;
                            FStar_TypeChecker_Env.Primops;
                            FStar_TypeChecker_Env.Unascribe] in
                          let norm_f =
                            let uu___ = FStar_Options.tactics_nbe () in
                            if uu___
                            then FStar_TypeChecker_NBE.normalize
                            else
                              FStar_TypeChecker_Normalize.normalize_with_primitive_steps in
                          let result =
                            let uu___ = primitive_steps () in
                            norm_f uu___ steps
                              proof_state.FStar_Tactics_Types.main_context tm in
                          let res =
                            unembed (FStar_Tactics_Embedding.e_result eb)
                              result ncb in
                          match res with
                          | FStar_Pervasives_Native.Some
                              (FStar_Tactics_Result.Success (b1, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStar_Tactics_Monad.set ps in
                                    FStar_Class_Monad.op_let_Bang
                                      FStar_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStar_Class_Monad.return
                                                 FStar_Tactics_Monad.monad_tac
                                                 () (Obj.magic b1))) uu___1)))
                          | FStar_Pervasives_Native.Some
                              (FStar_Tactics_Result.Failed (e, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStar_Tactics_Monad.set ps in
                                    FStar_Class_Monad.op_let_Bang
                                      FStar_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStar_Tactics_Monad.traise e))
                                           uu___1)))
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (let h_result = t_head_of result in
                                    let maybe_admit_tip =
                                      let r =
                                        Obj.magic
                                          (FStar_Syntax_VisitM.visitM_term
                                             FStar_Class_Monad.monad_option
                                             (fun uu___ ->
                                                (fun t ->
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv when
                                                       FStar_Syntax_Syntax.fv_eq_lid
                                                         fv
                                                         FStar_Parser_Const.admit_lid
                                                       ->
                                                       Obj.magic
                                                         FStar_Pervasives_Native.None
                                                   | uu___ ->
                                                       Obj.magic
                                                         (FStar_Pervasives_Native.Some
                                                            t)) uu___)
                                             h_result) in
                                      if
                                        FStar_Pervasives_Native.uu___is_None
                                          r
                                      then
                                        FStar_Pprint.doc_of_string
                                          "The term contains an `admit`, which will not reduce. Did you mean `tadmit()`?"
                                      else FStar_Pprint.empty in
                                    let uu___ =
                                      let uu___1 =
                                        let uu___2 =
                                          FStar_Errors_Raise.str
                                            "Tactic got stuck!" in
                                        let uu___3 =
                                          let uu___4 =
                                            let uu___5 =
                                              FStar_Errors_Raise.str
                                                "Reduction stopped at: " in
                                            let uu___6 =
                                              FStar_Errors_Raise.ttd h_result in
                                            FStar_Pprint.op_Hat_Hat uu___5
                                              uu___6 in
                                          [uu___4; maybe_admit_tip] in
                                        uu___2 :: uu___3 in
                                      (FStar_Errors_Codes.Fatal_TacticGotStuck,
                                        uu___1) in
                                    FStar_Errors_Raise.error_doc uu___
                                      (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))
                         uu___))) uu___2 uu___1 uu___
let unembed_tactic_nbe_0 :
  'b .
    'b FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'b FStar_Tactics_Monad.tac
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun eb ->
           fun cb ->
             fun embedded_tac_b ->
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                    () () (Obj.magic FStar_Tactics_Monad.get)
                    (fun uu___ ->
                       (fun proof_state ->
                          let proof_state = Obj.magic proof_state in
                          let result =
                            let uu___ =
                              let uu___1 =
                                let uu___2 =
                                  FStar_TypeChecker_NBETerm.embed
                                    FStar_Tactics_Embedding.e_proofstate_nbe
                                    cb proof_state in
                                FStar_TypeChecker_NBETerm.as_arg uu___2 in
                              [uu___1] in
                            FStar_TypeChecker_NBETerm.iapp_cb cb
                              embedded_tac_b uu___ in
                          let res =
                            FStar_TypeChecker_NBETerm.unembed
                              (FStar_Tactics_Embedding.e_result_nbe eb) cb
                              result in
                          match res with
                          | FStar_Pervasives_Native.Some
                              (FStar_Tactics_Result.Success (b1, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStar_Tactics_Monad.set ps in
                                    FStar_Class_Monad.op_let_Bang
                                      FStar_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStar_Class_Monad.return
                                                 FStar_Tactics_Monad.monad_tac
                                                 () (Obj.magic b1))) uu___1)))
                          | FStar_Pervasives_Native.Some
                              (FStar_Tactics_Result.Failed (e, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStar_Tactics_Monad.set ps in
                                    FStar_Class_Monad.op_let_Bang
                                      FStar_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStar_Tactics_Monad.traise e))
                                           uu___1)))
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ =
                                      let uu___1 =
                                        let uu___2 =
                                          FStar_Errors_Raise.str
                                            "Tactic got stuck (in NBE)!" in
                                        let uu___3 =
                                          let uu___4 =
                                            FStar_Errors_Msg.text
                                              "Please file a bug report with a minimal reproduction of this issue." in
                                          let uu___5 =
                                            let uu___6 =
                                              let uu___7 =
                                                FStar_Errors_Raise.str
                                                  "Result = " in
                                              let uu___8 =
                                                let uu___9 =
                                                  FStar_TypeChecker_NBETerm.t_to_string
                                                    result in
                                                FStar_Errors_Raise.str uu___9 in
                                              FStar_Pprint.op_Hat_Hat uu___7
                                                uu___8 in
                                            [uu___6] in
                                          uu___4 :: uu___5 in
                                        uu___2 :: uu___3 in
                                      (FStar_Errors_Codes.Fatal_TacticGotStuck,
                                        uu___1) in
                                    FStar_Errors_Raise.error_doc uu___
                                      (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))
                         uu___))) uu___2 uu___1 uu___
let unembed_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      'r FStar_Syntax_Embeddings_Base.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings_Base.norm_cb ->
            'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          fun x ->
            let rng = FStar_Compiler_Range_Type.dummyRange in
            let x_tm = embed ea rng x ncb in
            let app =
              let uu___ =
                let uu___1 = FStar_Syntax_Syntax.as_arg x_tm in [uu___1] in
              FStar_Syntax_Syntax.mk_Tm_app f uu___ rng in
            unembed_tactic_0 er app ncb
let unembed_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea ->
    fun er ->
      fun cb ->
        fun f ->
          fun x ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x in
            let app =
              let uu___ =
                let uu___1 = FStar_TypeChecker_NBETerm.as_arg x_tm in
                [uu___1] in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu___ in
            unembed_tactic_nbe_0 er cb app
let e_tactic_thunk :
  'r .
    'r FStar_Syntax_Embeddings_Base.embedding ->
      'r FStar_Tactics_Monad.tac FStar_Syntax_Embeddings_Base.embedding
  =
  fun er ->
    let uu___ =
      FStar_Syntax_Embeddings_Base.term_as_fv FStar_Syntax_Syntax.t_unit in
    FStar_Syntax_Embeddings_Base.mk_emb
      (fun uu___1 ->
         fun uu___2 ->
           fun uu___3 ->
             fun uu___4 ->
               FStar_Compiler_Effect.failwith
                 "Impossible: embedding tactic (thunk)?")
      (fun t ->
         fun cb ->
           let uu___1 =
             let uu___2 =
               unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb in
             uu___2 () in
           FStar_Pervasives_Native.Some uu___1) uu___
let e_tactic_nbe_thunk :
  'r .
    'r FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er ->
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb ->
         fun uu___ ->
           FStar_Compiler_Effect.failwith
             "Impossible: NBE embedding tactic (thunk)?")
      (fun cb ->
         fun t ->
           let uu___ =
             let uu___1 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t in
             uu___1 () in
           FStar_Pervasives_Native.Some uu___)
      (fun uu___ ->
         FStar_TypeChecker_NBETerm.mk_t
           (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit))
      (FStar_Syntax_Embeddings_Base.emb_typ_of FStar_Syntax_Embeddings.e_unit)
let e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      'r FStar_Syntax_Embeddings_Base.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun er ->
      let uu___ =
        FStar_Syntax_Embeddings_Base.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings_Base.mk_emb
        (fun uu___1 ->
           fun uu___2 ->
             fun uu___3 ->
               fun uu___4 ->
                 FStar_Compiler_Effect.failwith
                   "Impossible: embedding tactic (1)?")
        (fun t ->
           fun cb ->
             let uu___1 = unembed_tactic_1 ea er t cb in
             FStar_Pervasives_Native.Some uu___1) uu___
let e_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    fun er ->
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb ->
           fun uu___ ->
             FStar_Compiler_Effect.failwith
               "Impossible: NBE embedding tactic (1)?")
        (fun cb ->
           fun t ->
             let uu___ = unembed_tactic_nbe_1 ea er cb t in
             FStar_Pervasives_Native.Some uu___)
        (fun uu___ ->
           FStar_TypeChecker_NBETerm.mk_t
             (FStar_TypeChecker_NBETerm.Constant
                FStar_TypeChecker_NBETerm.Unit))
        (FStar_Syntax_Embeddings_Base.emb_typ_of
           FStar_Syntax_Embeddings.e_unit)
let unembed_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      'r FStar_Syntax_Embeddings_Base.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings_Base.norm_cb ->
            ('a -> 'r FStar_Tactics_Monad.tac) FStar_Pervasives_Native.option
  =
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          FStar_Pervasives_Native.Some
            (fun x ->
               let rng = FStar_Compiler_Range_Type.dummyRange in
               let x_tm = embed ea rng x ncb in
               let app =
                 let uu___ =
                   let uu___1 = FStar_Syntax_Syntax.as_arg x_tm in [uu___1] in
                 FStar_Syntax_Syntax.mk_Tm_app f uu___ rng in
               unembed_tactic_0 er app ncb)
let e_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      'r FStar_Syntax_Embeddings_Base.embedding ->
        ('a ->
           FStar_Tactics_Types.proofstate -> 'r FStar_Tactics_Result.__result)
          FStar_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun er ->
      let em uu___ uu___1 uu___2 uu___3 =
        FStar_Compiler_Effect.failwith "Impossible: embedding tactic (1)?" in
      let un t0 n =
        let uu___ = unembed_tactic_1_alt ea er t0 n in
        match uu___ with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x -> let uu___1 = f x in FStar_Tactics_Monad.run uu___1))
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu___ =
        FStar_Syntax_Embeddings_Base.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings_Base.mk_emb em un uu___
let (report_implicits :
  FStar_Compiler_Range_Type.range ->
    FStar_TypeChecker_Rel.tagged_implicits -> unit)
  =
  fun rng ->
    fun is ->
      FStar_Compiler_List.iter
        (fun uu___1 ->
           match uu___1 with
           | (imp, tag) ->
               (match tag with
                | FStar_TypeChecker_Rel.Implicit_unresolved ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            FStar_Errors_Msg.text
                              "Tactic left uninstantiated unification variable:" in
                          let uu___6 =
                            FStar_Class_PP.pp FStar_Syntax_Print.pretty_uvar
                              (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                          FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = FStar_Errors_Msg.text "Type:" in
                            let uu___8 =
                              let uu___9 =
                                FStar_Syntax_Util.ctx_uvar_typ
                                  imp.FStar_TypeChecker_Common.imp_uvar in
                              FStar_Class_PP.pp
                                FStar_Syntax_Print.pretty_term uu___9 in
                            FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                          let uu___7 =
                            let uu___8 =
                              let uu___9 = FStar_Errors_Msg.text "Reason:" in
                              let uu___10 =
                                let uu___11 =
                                  FStar_Pprint.doc_of_string
                                    imp.FStar_TypeChecker_Common.imp_reason in
                                FStar_Pprint.dquotes uu___11 in
                              FStar_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                            [uu___8] in
                          uu___6 :: uu___7 in
                        uu___4 :: uu___5 in
                      (FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic,
                        uu___3) in
                    FStar_Errors.log_issue_doc rng uu___2
                | FStar_TypeChecker_Rel.Implicit_checking_defers_univ_constraint
                    ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            FStar_Errors_Msg.text
                              "Tactic left uninstantiated unification variable:" in
                          let uu___6 =
                            FStar_Class_PP.pp FStar_Syntax_Print.pretty_uvar
                              (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                          FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = FStar_Errors_Msg.text "Type:" in
                            let uu___8 =
                              let uu___9 =
                                FStar_Syntax_Util.ctx_uvar_typ
                                  imp.FStar_TypeChecker_Common.imp_uvar in
                              FStar_Class_PP.pp
                                FStar_Syntax_Print.pretty_term uu___9 in
                            FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                          let uu___7 =
                            let uu___8 =
                              let uu___9 = FStar_Errors_Msg.text "Reason:" in
                              let uu___10 =
                                let uu___11 =
                                  FStar_Pprint.doc_of_string
                                    imp.FStar_TypeChecker_Common.imp_reason in
                                FStar_Pprint.dquotes uu___11 in
                              FStar_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                            [uu___8] in
                          uu___6 :: uu___7 in
                        uu___4 :: uu___5 in
                      (FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic,
                        uu___3) in
                    FStar_Errors.log_issue_doc rng uu___2
                | FStar_TypeChecker_Rel.Implicit_has_typing_guard (tm, ty) ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            FStar_Errors_Msg.text "Tactic solved goal:" in
                          let uu___6 =
                            FStar_Class_PP.pp FStar_Syntax_Print.pretty_uvar
                              (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                          FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = FStar_Errors_Msg.text "Type:" in
                            let uu___8 =
                              let uu___9 =
                                FStar_Syntax_Util.ctx_uvar_typ
                                  imp.FStar_TypeChecker_Common.imp_uvar in
                              FStar_Class_PP.pp
                                FStar_Syntax_Print.pretty_term uu___9 in
                            FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStar_Errors_Msg.text "To the term:" in
                              let uu___10 =
                                FStar_Class_PP.pp
                                  FStar_Syntax_Print.pretty_term tm in
                              FStar_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                            let uu___9 =
                              let uu___10 =
                                FStar_Errors_Msg.text
                                  "But it has a non-trivial typing guard. Use gather_or_solve_explicit_guards_for_resolved_goals to inspect and prove these goals" in
                              [uu___10] in
                            uu___8 :: uu___9 in
                          uu___6 :: uu___7 in
                        uu___4 :: uu___5 in
                      (FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic,
                        uu___3) in
                    FStar_Errors.log_issue_doc rng uu___2)) is;
      FStar_Errors.stop_if_err ()
let run_unembedded_tactic_on_ps :
  'a 'b .
    FStar_Compiler_Range_Type.range ->
      FStar_Compiler_Range_Type.range ->
        Prims.bool ->
          'a ->
            ('a -> 'b FStar_Tactics_Monad.tac) ->
              FStar_Tactics_Types.proofstate ->
                (FStar_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_call ->
    fun rng_goal ->
      fun background ->
        fun arg ->
          fun tau ->
            fun ps ->
              let ps1 =
                {
                  FStar_Tactics_Types.main_context =
                    (let uu___ = ps.FStar_Tactics_Types.main_context in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.intactics = true;
                       FStar_TypeChecker_Env.nocoerce =
                         (uu___.FStar_TypeChecker_Env.nocoerce);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (uu___.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (uu___.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStar_TypeChecker_Env.teq_nosmt_force =
                         (uu___.FStar_TypeChecker_Env.teq_nosmt_force);
                       FStar_TypeChecker_Env.subtype_nosmt_force =
                         (uu___.FStar_TypeChecker_Env.subtype_nosmt_force);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___.FStar_TypeChecker_Env.unif_allow_ref_guards);
                       FStar_TypeChecker_Env.erase_erasable_args =
                         (uu___.FStar_TypeChecker_Env.erase_erasable_args);
                       FStar_TypeChecker_Env.core_check =
                         (uu___.FStar_TypeChecker_Env.core_check)
                     });
                  FStar_Tactics_Types.all_implicits =
                    (ps.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
                  FStar_Tactics_Types.smt_goals =
                    (ps.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (ps.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (ps.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (ps.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (ps.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (ps.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (ps.FStar_Tactics_Types.local_state);
                  FStar_Tactics_Types.urgency =
                    (ps.FStar_Tactics_Types.urgency);
                  FStar_Tactics_Types.dump_on_failure =
                    (ps.FStar_Tactics_Types.dump_on_failure)
                } in
              let ps2 =
                {
                  FStar_Tactics_Types.main_context =
                    (let uu___ = ps1.FStar_Tactics_Types.main_context in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range = rng_goal;
                       FStar_TypeChecker_Env.curmodule =
                         (uu___.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.intactics =
                         (uu___.FStar_TypeChecker_Env.intactics);
                       FStar_TypeChecker_Env.nocoerce =
                         (uu___.FStar_TypeChecker_Env.nocoerce);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (uu___.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (uu___.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStar_TypeChecker_Env.teq_nosmt_force =
                         (uu___.FStar_TypeChecker_Env.teq_nosmt_force);
                       FStar_TypeChecker_Env.subtype_nosmt_force =
                         (uu___.FStar_TypeChecker_Env.subtype_nosmt_force);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___.FStar_TypeChecker_Env.unif_allow_ref_guards);
                       FStar_TypeChecker_Env.erase_erasable_args =
                         (uu___.FStar_TypeChecker_Env.erase_erasable_args);
                       FStar_TypeChecker_Env.core_check =
                         (uu___.FStar_TypeChecker_Env.core_check)
                     });
                  FStar_Tactics_Types.all_implicits =
                    (ps1.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (ps1.FStar_Tactics_Types.goals);
                  FStar_Tactics_Types.smt_goals =
                    (ps1.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth = (ps1.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (ps1.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc = (ps1.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (ps1.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (ps1.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (ps1.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (ps1.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (ps1.FStar_Tactics_Types.local_state);
                  FStar_Tactics_Types.urgency =
                    (ps1.FStar_Tactics_Types.urgency);
                  FStar_Tactics_Types.dump_on_failure =
                    (ps1.FStar_Tactics_Types.dump_on_failure)
                } in
              let env = ps2.FStar_Tactics_Types.main_context in
              let res =
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      FStar_TypeChecker_Env.current_module
                        ps2.FStar_Tactics_Types.main_context in
                    FStar_Ident.string_of_lid uu___2 in
                  FStar_Pervasives_Native.Some uu___1 in
                FStar_Profiling.profile
                  (fun uu___1 ->
                     let uu___2 = tau arg in
                     FStar_Tactics_Monad.run_safe uu___2 ps2) uu___
                  "FStar.Tactics.Interpreter.run_safe" in
              (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_Tac in
               if uu___1 then FStar_Compiler_Util.print_string "}\n" else ());
              (match res with
               | FStar_Tactics_Result.Success (ret, ps3) ->
                   ((let uu___2 = FStar_Compiler_Effect.op_Bang dbg_Tac in
                     if uu___2
                     then
                       FStar_Tactics_Printing.do_dump_proofstate ps3
                         "at the finish line"
                     else ());
                    (let remaining_smt_goals =
                       FStar_Compiler_List.op_At
                         ps3.FStar_Tactics_Types.goals
                         ps3.FStar_Tactics_Types.smt_goals in
                     FStar_Compiler_List.iter
                       (fun g ->
                          FStar_Tactics_Monad.mark_goal_implicit_already_checked
                            g;
                          (let uu___4 = FStar_Tactics_Monad.is_irrelevant g in
                           if uu___4
                           then
                             ((let uu___6 =
                                 FStar_Compiler_Effect.op_Bang dbg_Tac in
                               if uu___6
                               then
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Tactics_Types.goal_witness g in
                                   FStar_Class_Show.show
                                     FStar_Syntax_Print.showable_term uu___8 in
                                 FStar_Compiler_Util.print1
                                   "Assigning irrelevant goal %s\n" uu___7
                               else ());
                              (let uu___6 =
                                 let uu___7 = FStar_Tactics_Types.goal_env g in
                                 let uu___8 =
                                   FStar_Tactics_Types.goal_witness g in
                                 FStar_TypeChecker_Rel.teq_nosmt_force uu___7
                                   uu___8 FStar_Syntax_Util.exp_unit in
                               if uu___6
                               then ()
                               else
                                 (let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_Tactics_Types.goal_witness g in
                                      FStar_Class_Show.show
                                        FStar_Syntax_Print.showable_term
                                        uu___10 in
                                    FStar_Compiler_Util.format1
                                      "Irrelevant tactic witness does not unify with (): %s"
                                      uu___9 in
                                  FStar_Compiler_Effect.failwith uu___8)))
                           else ())) remaining_smt_goals;
                     FStar_Errors.with_ctx
                       "While checking implicits left by a tactic"
                       (fun uu___4 ->
                          (let uu___6 = FStar_Compiler_Effect.op_Bang dbg_Tac in
                           if uu___6
                           then
                             let uu___7 =
                               (FStar_Common.string_of_list ())
                                 (fun imp ->
                                    FStar_Class_Show.show
                                      FStar_Syntax_Print.showable_ctxu
                                      imp.FStar_TypeChecker_Common.imp_uvar)
                                 ps3.FStar_Tactics_Types.all_implicits in
                             FStar_Compiler_Util.print1
                               "About to check tactic implicits: %s\n" uu___7
                           else ());
                          (let g =
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred_to_tac =
                                 (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                               FStar_TypeChecker_Common.deferred =
                                 (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                               FStar_TypeChecker_Common.implicits =
                                 (ps3.FStar_Tactics_Types.all_implicits)
                             } in
                           let g1 =
                             FStar_TypeChecker_Rel.solve_deferred_constraints
                               env g in
                           (let uu___7 =
                              FStar_Compiler_Effect.op_Bang dbg_Tac in
                            if uu___7
                            then
                              let uu___8 =
                                FStar_Class_Show.show
                                  (FStar_Class_Show.printableshow
                                     FStar_Class_Printable.printable_nat)
                                  (FStar_Compiler_List.length
                                     ps3.FStar_Tactics_Types.all_implicits) in
                              let uu___9 =
                                FStar_Class_Show.show
                                  (FStar_Class_Show.show_list
                                     FStar_TypeChecker_Common.show_implicit)
                                  ps3.FStar_Tactics_Types.all_implicits in
                              FStar_Compiler_Util.print2
                                "Checked %s implicits (1): %s\n" uu___8
                                uu___9
                            else ());
                           (let tagged_implicits =
                              FStar_TypeChecker_Rel.resolve_implicits_tac env
                                g1 in
                            (let uu___8 =
                               FStar_Compiler_Effect.op_Bang dbg_Tac in
                             if uu___8
                             then
                               let uu___9 =
                                 FStar_Class_Show.show
                                   (FStar_Class_Show.printableshow
                                      FStar_Class_Printable.printable_nat)
                                   (FStar_Compiler_List.length
                                      ps3.FStar_Tactics_Types.all_implicits) in
                               let uu___10 =
                                 FStar_Class_Show.show
                                   (FStar_Class_Show.show_list
                                      FStar_TypeChecker_Common.show_implicit)
                                   ps3.FStar_Tactics_Types.all_implicits in
                               FStar_Compiler_Util.print2
                                 "Checked %s implicits (2): %s\n" uu___9
                                 uu___10
                             else ());
                            report_implicits rng_goal tagged_implicits)));
                     (remaining_smt_goals, ret)))
               | FStar_Tactics_Result.Failed
                   (FStar_Errors.Error (code, msg, rng, ctx), ps3) ->
                   let msg1 =
                     let uu___1 = FStar_Pprint.doc_of_string "Tactic failed" in
                     uu___1 :: msg in
                   FStar_Compiler_Effect.raise
                     (FStar_Errors.Error (code, msg1, rng, ctx))
               | FStar_Tactics_Result.Failed
                   (FStar_Errors.Err (code, msg, ctx), ps3) ->
                   let msg1 =
                     let uu___1 = FStar_Pprint.doc_of_string "Tactic failed" in
                     uu___1 :: msg in
                   FStar_Compiler_Effect.raise
                     (FStar_Errors.Err (code, msg1, ctx))
               | FStar_Tactics_Result.Failed (e, ps3) ->
                   (if ps3.FStar_Tactics_Types.dump_on_failure
                    then
                      FStar_Tactics_Printing.do_dump_proofstate ps3
                        "at the time of failure"
                    else ();
                    (let texn_to_doc e1 =
                       match e1 with
                       | FStar_Tactics_Common.TacticFailure msg -> msg
                       | FStar_Tactics_Common.EExn t ->
                           let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 FStar_Class_Show.show
                                   FStar_Syntax_Print.showable_term t in
                               Prims.strcat "Uncaught exception: " uu___4 in
                             FStar_Pprint.doc_of_string uu___3 in
                           [uu___2]
                       | e2 -> FStar_Compiler_Effect.raise e2 in
                     let rng =
                       if background
                       then
                         match ps3.FStar_Tactics_Types.goals with
                         | g::uu___2 ->
                             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
                         | uu___2 -> rng_call
                       else ps3.FStar_Tactics_Types.entry_range in
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStar_Pprint.doc_of_string "Tactic failed" in
                           [uu___5] in
                         let uu___5 = texn_to_doc e in
                         FStar_Compiler_List.op_At uu___4 uu___5 in
                       (FStar_Errors_Codes.Fatal_UserTacticFailure, uu___3) in
                     FStar_Errors.raise_error_doc uu___2 rng)))
let run_tactic_on_ps' :
  'a 'b .
    FStar_Compiler_Range_Type.range ->
      FStar_Compiler_Range_Type.range ->
        Prims.bool ->
          'a FStar_Syntax_Embeddings_Base.embedding ->
            'a ->
              'b FStar_Syntax_Embeddings_Base.embedding ->
                FStar_Syntax_Syntax.term ->
                  Prims.bool ->
                    FStar_Tactics_Types.proofstate ->
                      (FStar_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_call ->
    fun rng_goal ->
      fun background ->
        fun e_arg ->
          fun arg ->
            fun e_res ->
              fun tactic ->
                fun tactic_already_typed ->
                  fun ps ->
                    let env = ps.FStar_Tactics_Types.main_context in
                    (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_Tac in
                     if uu___1
                     then
                       let uu___2 =
                         FStar_Class_Show.show
                           FStar_Syntax_Print.showable_term tactic in
                       let uu___3 =
                         FStar_Class_Show.show
                           (FStar_Class_Show.printableshow
                              FStar_Class_Printable.printable_bool)
                           tactic_already_typed in
                       FStar_Compiler_Util.print2
                         "Typechecking tactic: (%s) (already_typed: %s) {\n"
                         uu___2 uu___3
                     else ());
                    (let g =
                       if tactic_already_typed
                       then FStar_TypeChecker_Env.trivial_guard
                       else
                         (let uu___2 =
                            let uu___3 =
                              FStar_Syntax_Embeddings_Base.type_of e_arg in
                            let uu___4 =
                              FStar_Syntax_Embeddings_Base.type_of e_res in
                            FStar_TypeChecker_TcTerm.tc_tactic uu___3 uu___4
                              env tactic in
                          match uu___2 with | (uu___3, uu___4, g1) -> g1) in
                     (let uu___2 = FStar_Compiler_Effect.op_Bang dbg_Tac in
                      if uu___2
                      then FStar_Compiler_Util.print_string "}\n"
                      else ());
                     FStar_TypeChecker_Rel.force_trivial_guard env g;
                     FStar_Errors.stop_if_err ();
                     (let tau =
                        unembed_tactic_1 e_arg e_res tactic
                          FStar_Syntax_Embeddings_Base.id_norm_cb in
                      run_unembedded_tactic_on_ps rng_call rng_goal
                        background arg tau ps))
let run_tactic_on_ps :
  'a 'b .
    FStar_Compiler_Range_Type.range ->
      FStar_Compiler_Range_Type.range ->
        Prims.bool ->
          'a FStar_Syntax_Embeddings_Base.embedding ->
            'a ->
              'b FStar_Syntax_Embeddings_Base.embedding ->
                FStar_Syntax_Syntax.term ->
                  Prims.bool ->
                    FStar_Tactics_Types.proofstate ->
                      (FStar_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_call ->
    fun rng_goal ->
      fun background ->
        fun e_arg ->
          fun arg ->
            fun e_res ->
              fun tactic ->
                fun tactic_already_typed ->
                  fun ps ->
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          FStar_TypeChecker_Env.current_module
                            ps.FStar_Tactics_Types.main_context in
                        FStar_Ident.string_of_lid uu___2 in
                      FStar_Pervasives_Native.Some uu___1 in
                    FStar_Profiling.profile
                      (fun uu___1 ->
                         run_tactic_on_ps' rng_call rng_goal background e_arg
                           arg e_res tactic tactic_already_typed ps) uu___
                      "FStar.Tactics.Interpreter.run_tactic_on_ps"