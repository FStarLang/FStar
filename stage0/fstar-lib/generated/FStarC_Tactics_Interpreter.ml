open Prims
let (dbg_Tac : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Tac"
let solve : 'a . 'a -> 'a = fun ev -> ev
let embed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Compiler_Range_Type.range ->
        'a ->
          FStarC_Syntax_Embeddings_Base.norm_cb -> FStarC_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu___1 = FStarC_Syntax_Embeddings_Base.embed uu___ x in
          uu___1 r FStar_Pervasives_Native.None norm_cb
let unembed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Embeddings_Base.norm_cb ->
          'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun a1 ->
      fun norm_cb -> FStarC_Syntax_Embeddings_Base.unembed uu___ a1 norm_cb
let (native_tactics_steps :
  unit -> FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  fun uu___ ->
    let step_from_native_step s =
      {
        FStarC_TypeChecker_Primops_Base.name = (s.FStarC_Tactics_Native.name);
        FStarC_TypeChecker_Primops_Base.arity =
          (s.FStarC_Tactics_Native.arity);
        FStarC_TypeChecker_Primops_Base.univ_arity = Prims.int_zero;
        FStarC_TypeChecker_Primops_Base.auto_reflect =
          (FStar_Pervasives_Native.Some
             (s.FStarC_Tactics_Native.arity - Prims.int_one));
        FStarC_TypeChecker_Primops_Base.strong_reduction_ok =
          (s.FStarC_Tactics_Native.strong_reduction_ok);
        FStarC_TypeChecker_Primops_Base.requires_binder_substitution = false;
        FStarC_TypeChecker_Primops_Base.renorm_after = false;
        FStarC_TypeChecker_Primops_Base.interpretation =
          (s.FStarC_Tactics_Native.tactic);
        FStarC_TypeChecker_Primops_Base.interpretation_nbe =
          (fun _cb ->
             fun _us ->
               FStarC_TypeChecker_NBETerm.dummy_interp
                 s.FStarC_Tactics_Native.name)
      } in
    let uu___1 = FStarC_Tactics_Native.list_all () in
    FStarC_Compiler_List.map step_from_native_step uu___1
let (__primitive_steps_ref :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref []
let (primitive_steps :
  unit -> FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  fun uu___ ->
    let uu___1 = native_tactics_steps () in
    let uu___2 = FStarC_Compiler_Effect.op_Bang __primitive_steps_ref in
    FStarC_Compiler_List.op_At uu___1 uu___2
let (register_tactic_primitive_step :
  FStarC_TypeChecker_Primops_Base.primitive_step -> unit) =
  fun s ->
    let uu___ =
      let uu___1 = FStarC_Compiler_Effect.op_Bang __primitive_steps_ref in s
        :: uu___1 in
    FStarC_Compiler_Effect.op_Colon_Equals __primitive_steps_ref uu___
let rec (t_head_of : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_app uu___1 ->
        let uu___2 = FStarC_Syntax_Util.head_and_args_full t in
        (match uu___2 with
         | (h, args) ->
             let h1 = FStarC_Syntax_Util.unmeta h in
             let uu___3 =
               let uu___4 = FStarC_Syntax_Subst.compress h1 in
               uu___4.FStarC_Syntax_Syntax.n in
             (match uu___3 with
              | FStarC_Syntax_Syntax.Tm_uinst uu___4 -> t
              | FStarC_Syntax_Syntax.Tm_fvar uu___4 -> t
              | FStarC_Syntax_Syntax.Tm_bvar uu___4 -> t
              | FStarC_Syntax_Syntax.Tm_name uu___4 -> t
              | FStarC_Syntax_Syntax.Tm_constant uu___4 -> t
              | uu___4 -> t_head_of h1))
    | FStarC_Syntax_Syntax.Tm_match
        { FStarC_Syntax_Syntax.scrutinee = t1;
          FStarC_Syntax_Syntax.ret_opt = uu___1;
          FStarC_Syntax_Syntax.brs = uu___2;
          FStarC_Syntax_Syntax.rc_opt1 = uu___3;_}
        -> t_head_of t1
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = uu___1;
          FStarC_Syntax_Syntax.eff_opt = uu___2;_}
        -> t_head_of t1
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t1;
          FStarC_Syntax_Syntax.meta = uu___1;_}
        -> t_head_of t1
    | uu___1 -> t
let unembed_tactic_0 :
  'b .
    'b FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Embeddings_Base.norm_cb -> 'b FStarC_Tactics_Monad.tac
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun eb ->
           fun embedded_tac_b ->
             fun ncb ->
               Obj.magic
                 (FStarC_Class_Monad.op_let_Bang
                    FStarC_Tactics_Monad.monad_tac () ()
                    (Obj.magic FStarC_Tactics_Monad.get)
                    (fun uu___ ->
                       (fun proof_state ->
                          let proof_state = Obj.magic proof_state in
                          let rng = embedded_tac_b.FStarC_Syntax_Syntax.pos in
                          let embedded_tac_b1 =
                            FStarC_Syntax_Util.mk_reify embedded_tac_b
                              (FStar_Pervasives_Native.Some
                                 FStarC_Parser_Const.effect_TAC_lid) in
                          let tm =
                            let uu___ =
                              let uu___1 =
                                let uu___2 =
                                  embed FStarC_Tactics_Embedding.e_proofstate
                                    rng proof_state ncb in
                                FStarC_Syntax_Syntax.as_arg uu___2 in
                              [uu___1] in
                            FStarC_Syntax_Syntax.mk_Tm_app embedded_tac_b1
                              uu___ rng in
                          let steps =
                            [FStarC_TypeChecker_Env.Weak;
                            FStarC_TypeChecker_Env.Reify;
                            FStarC_TypeChecker_Env.UnfoldUntil
                              FStarC_Syntax_Syntax.delta_constant;
                            FStarC_TypeChecker_Env.DontUnfoldAttr
                              [FStarC_Parser_Const.tac_opaque_attr];
                            FStarC_TypeChecker_Env.Primops;
                            FStarC_TypeChecker_Env.Unascribe;
                            FStarC_TypeChecker_Env.Tactics] in
                          let norm_f =
                            let uu___ = FStarC_Options.tactics_nbe () in
                            if uu___
                            then FStarC_TypeChecker_NBE.normalize
                            else
                              FStarC_TypeChecker_Normalize.normalize_with_primitive_steps in
                          let result =
                            let uu___ = primitive_steps () in
                            norm_f uu___ steps
                              proof_state.FStarC_Tactics_Types.main_context
                              tm in
                          let res =
                            unembed (FStarC_Tactics_Embedding.e_result eb)
                              result ncb in
                          match res with
                          | FStar_Pervasives_Native.Some
                              (FStarC_Tactics_Result.Success (b1, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStarC_Tactics_Monad.set ps in
                                    FStarC_Class_Monad.op_let_Bang
                                      FStarC_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.return
                                                 FStarC_Tactics_Monad.monad_tac
                                                 () (Obj.magic b1))) uu___1)))
                          | FStar_Pervasives_Native.Some
                              (FStarC_Tactics_Result.Failed (e, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStarC_Tactics_Monad.set ps in
                                    FStarC_Class_Monad.op_let_Bang
                                      FStarC_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStarC_Tactics_Monad.traise e))
                                           uu___1)))
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (let h_result = t_head_of result in
                                    let maybe_admit_tip =
                                      let r =
                                        Obj.magic
                                          (FStarC_Syntax_VisitM.visitM_term
                                             FStarC_Class_Monad.monad_option
                                             false
                                             (fun uu___ ->
                                                (fun t ->
                                                   match t.FStarC_Syntax_Syntax.n
                                                   with
                                                   | FStarC_Syntax_Syntax.Tm_fvar
                                                       fv when
                                                       FStarC_Syntax_Syntax.fv_eq_lid
                                                         fv
                                                         FStarC_Parser_Const.admit_lid
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
                                        FStarC_Pprint.doc_of_string
                                          "The term contains an `admit`, which will not reduce. Did you mean `tadmit()`?"
                                      else FStarC_Pprint.empty in
                                    let uu___ =
                                      let uu___1 =
                                        FStarC_Pprint.doc_of_string
                                          "Tactic got stuck!" in
                                      let uu___2 =
                                        let uu___3 =
                                          let uu___4 =
                                            FStarC_Pprint.doc_of_string
                                              "Reduction stopped at:" in
                                          let uu___5 =
                                            FStarC_Class_PP.pp
                                              FStarC_Syntax_Print.pretty_term
                                              h_result in
                                          FStarC_Pprint.prefix
                                            (Prims.of_int (2)) Prims.int_one
                                            uu___4 uu___5 in
                                        [uu___3; maybe_admit_tip] in
                                      uu___1 :: uu___2 in
                                    FStarC_Errors.raise_error
                                      FStarC_TypeChecker_Env.hasRange_env
                                      proof_state.FStarC_Tactics_Types.main_context
                                      FStarC_Errors_Codes.Fatal_TacticGotStuck
                                      ()
                                      (Obj.magic
                                         FStarC_Errors_Msg.is_error_message_list_doc)
                                      (Obj.magic uu___)))) uu___))) uu___2
          uu___1 uu___
let unembed_tactic_nbe_0 :
  'b .
    'b FStarC_TypeChecker_NBETerm.embedding ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        FStarC_TypeChecker_NBETerm.t -> 'b FStarC_Tactics_Monad.tac
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun eb ->
           fun cb ->
             fun embedded_tac_b ->
               Obj.magic
                 (FStarC_Class_Monad.op_let_Bang
                    FStarC_Tactics_Monad.monad_tac () ()
                    (Obj.magic FStarC_Tactics_Monad.get)
                    (fun uu___ ->
                       (fun proof_state ->
                          let proof_state = Obj.magic proof_state in
                          let result =
                            let uu___ =
                              let uu___1 =
                                let uu___2 =
                                  FStarC_TypeChecker_NBETerm.embed
                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                    cb proof_state in
                                FStarC_TypeChecker_NBETerm.as_arg uu___2 in
                              [uu___1] in
                            FStarC_TypeChecker_NBETerm.iapp_cb cb
                              embedded_tac_b uu___ in
                          let res =
                            FStarC_TypeChecker_NBETerm.unembed
                              (FStarC_Tactics_Embedding.e_result_nbe eb) cb
                              result in
                          match res with
                          | FStar_Pervasives_Native.Some
                              (FStarC_Tactics_Result.Success (b1, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStarC_Tactics_Monad.set ps in
                                    FStarC_Class_Monad.op_let_Bang
                                      FStarC_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.return
                                                 FStarC_Tactics_Monad.monad_tac
                                                 () (Obj.magic b1))) uu___1)))
                          | FStar_Pervasives_Native.Some
                              (FStarC_Tactics_Result.Failed (e, ps)) ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ = FStarC_Tactics_Monad.set ps in
                                    FStarC_Class_Monad.op_let_Bang
                                      FStarC_Tactics_Monad.monad_tac () ()
                                      uu___
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            let uu___1 = Obj.magic uu___1 in
                                            Obj.magic
                                              (FStarC_Tactics_Monad.traise e))
                                           uu___1)))
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___ =
                                      let uu___1 =
                                        FStarC_Pprint.doc_of_string
                                          "Tactic got stuck (in NBE)!" in
                                      let uu___2 =
                                        let uu___3 =
                                          FStarC_Errors_Msg.text
                                            "Please file a bug report with a minimal reproduction of this issue." in
                                        let uu___4 =
                                          let uu___5 =
                                            let uu___6 =
                                              FStarC_Pprint.doc_of_string
                                                "Result = " in
                                            let uu___7 =
                                              let uu___8 =
                                                FStarC_TypeChecker_NBETerm.t_to_string
                                                  result in
                                              FStarC_Pprint.arbitrary_string
                                                uu___8 in
                                            FStarC_Pprint.op_Hat_Hat uu___6
                                              uu___7 in
                                          [uu___5] in
                                        uu___3 :: uu___4 in
                                      uu___1 :: uu___2 in
                                    FStarC_Errors.raise_error
                                      FStarC_TypeChecker_Env.hasRange_env
                                      proof_state.FStarC_Tactics_Types.main_context
                                      FStarC_Errors_Codes.Fatal_TacticGotStuck
                                      ()
                                      (Obj.magic
                                         FStarC_Errors_Msg.is_error_message_list_doc)
                                      (Obj.magic uu___)))) uu___))) uu___2
          uu___1 uu___
let unembed_tactic_1 :
  'a 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'r FStarC_Syntax_Embeddings_Base.embedding ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Embeddings_Base.norm_cb ->
            'a -> 'r FStarC_Tactics_Monad.tac
  =
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          fun x ->
            let rng = FStarC_Compiler_Range_Type.dummyRange in
            let x_tm = embed ea rng x ncb in
            let app =
              let uu___ =
                let uu___1 = FStarC_Syntax_Syntax.as_arg x_tm in [uu___1] in
              FStarC_Syntax_Syntax.mk_Tm_app f uu___ rng in
            unembed_tactic_0 er app ncb
let unembed_tactic_nbe_1 :
  'a 'r .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'r FStarC_TypeChecker_NBETerm.embedding ->
        FStarC_TypeChecker_NBETerm.nbe_cbs ->
          FStarC_TypeChecker_NBETerm.t -> 'a -> 'r FStarC_Tactics_Monad.tac
  =
  fun ea ->
    fun er ->
      fun cb ->
        fun f ->
          fun x ->
            let x_tm = FStarC_TypeChecker_NBETerm.embed ea cb x in
            let app =
              let uu___ =
                let uu___1 = FStarC_TypeChecker_NBETerm.as_arg x_tm in
                [uu___1] in
              FStarC_TypeChecker_NBETerm.iapp_cb cb f uu___ in
            unembed_tactic_nbe_0 er cb app
let e_tactic_thunk :
  'r .
    'r FStarC_Syntax_Embeddings_Base.embedding ->
      'r FStarC_Tactics_Monad.tac FStarC_Syntax_Embeddings_Base.embedding
  =
  fun er ->
    let uu___ =
      FStarC_Syntax_Embeddings_Base.term_as_fv FStarC_Syntax_Syntax.t_unit in
    FStarC_Syntax_Embeddings_Base.mk_emb
      (fun uu___1 ->
         fun uu___2 ->
           fun uu___3 ->
             fun uu___4 -> failwith "Impossible: embedding tactic (thunk)?")
      (fun t ->
         fun cb ->
           let uu___1 =
             let uu___2 =
               unembed_tactic_1 FStarC_Syntax_Embeddings.e_unit er t cb in
             uu___2 () in
           FStar_Pervasives_Native.Some uu___1) uu___
let e_tactic_nbe_thunk :
  'r .
    'r FStarC_TypeChecker_NBETerm.embedding ->
      'r FStarC_Tactics_Monad.tac FStarC_TypeChecker_NBETerm.embedding
  =
  fun er ->
    FStarC_TypeChecker_NBETerm.mk_emb
      (fun cb ->
         fun uu___ -> failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb ->
         fun t ->
           let uu___ =
             let uu___1 =
               unembed_tactic_nbe_1 FStarC_TypeChecker_NBETerm.e_unit er cb t in
             uu___1 () in
           FStar_Pervasives_Native.Some uu___)
      (fun uu___ ->
         FStarC_TypeChecker_NBETerm.mk_t
           (FStarC_TypeChecker_NBETerm.Constant
              FStarC_TypeChecker_NBETerm.Unit))
      (FStarC_Syntax_Embeddings_Base.emb_typ_of
         FStarC_Syntax_Embeddings.e_unit)
let e_tactic_1 :
  'a 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'r FStarC_Syntax_Embeddings_Base.embedding ->
        ('a -> 'r FStarC_Tactics_Monad.tac)
          FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun er ->
      let uu___ =
        FStarC_Syntax_Embeddings_Base.term_as_fv FStarC_Syntax_Syntax.t_unit in
      FStarC_Syntax_Embeddings_Base.mk_emb
        (fun uu___1 ->
           fun uu___2 ->
             fun uu___3 ->
               fun uu___4 -> failwith "Impossible: embedding tactic (1)?")
        (fun t ->
           fun cb ->
             let uu___1 = unembed_tactic_1 ea er t cb in
             FStar_Pervasives_Native.Some uu___1) uu___
let e_tactic_nbe_1 :
  'a 'r .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'r FStarC_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStarC_Tactics_Monad.tac)
          FStarC_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    fun er ->
      FStarC_TypeChecker_NBETerm.mk_emb
        (fun cb ->
           fun uu___ -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb ->
           fun t ->
             let uu___ = unembed_tactic_nbe_1 ea er cb t in
             FStar_Pervasives_Native.Some uu___)
        (fun uu___ ->
           FStarC_TypeChecker_NBETerm.mk_t
             (FStarC_TypeChecker_NBETerm.Constant
                FStarC_TypeChecker_NBETerm.Unit))
        (FStarC_Syntax_Embeddings_Base.emb_typ_of
           FStarC_Syntax_Embeddings.e_unit)
let unembed_tactic_1_alt :
  'a 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'r FStarC_Syntax_Embeddings_Base.embedding ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Embeddings_Base.norm_cb ->
            ('a -> 'r FStarC_Tactics_Monad.tac)
              FStar_Pervasives_Native.option
  =
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          FStar_Pervasives_Native.Some
            (fun x ->
               let rng = FStarC_Compiler_Range_Type.dummyRange in
               let x_tm = embed ea rng x ncb in
               let app =
                 let uu___ =
                   let uu___1 = FStarC_Syntax_Syntax.as_arg x_tm in [uu___1] in
                 FStarC_Syntax_Syntax.mk_Tm_app f uu___ rng in
               unembed_tactic_0 er app ncb)
let e_tactic_1_alt :
  'a 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'r FStarC_Syntax_Embeddings_Base.embedding ->
        ('a ->
           FStarC_Tactics_Types.proofstate ->
             'r FStarC_Tactics_Result.__result)
          FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun er ->
      let em uu___ uu___1 uu___2 uu___3 =
        failwith "Impossible: embedding tactic (1)?" in
      let un t0 n =
        let uu___ = unembed_tactic_1_alt ea er t0 n in
        match uu___ with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x -> let uu___1 = f x in FStarC_Tactics_Monad.run uu___1))
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu___ =
        FStarC_Syntax_Embeddings_Base.term_as_fv FStarC_Syntax_Syntax.t_unit in
      FStarC_Syntax_Embeddings_Base.mk_emb em un uu___
let (report_implicits :
  FStarC_Compiler_Range_Type.range ->
    FStarC_TypeChecker_Rel.tagged_implicits -> unit)
  =
  fun rng ->
    fun is ->
      FStarC_Compiler_List.iter
        (fun uu___1 ->
           match uu___1 with
           | (imp, tag) ->
               (match tag with
                | FStarC_TypeChecker_Rel.Implicit_unresolved ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_Errors_Msg.text
                            "Tactic left uninstantiated unification variable:" in
                        let uu___5 =
                          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_uvar
                            (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStarC_Errors_Msg.text "Type:" in
                          let uu___7 =
                            let uu___8 =
                              FStarC_Syntax_Util.ctx_uvar_typ
                                imp.FStarC_TypeChecker_Common.imp_uvar in
                            FStarC_Class_PP.pp
                              FStarC_Syntax_Print.pretty_term uu___8 in
                          FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStarC_Errors_Msg.text "Reason:" in
                            let uu___9 =
                              let uu___10 =
                                FStarC_Pprint.doc_of_string
                                  imp.FStarC_TypeChecker_Common.imp_reason in
                              FStarC_Pprint.dquotes uu___10 in
                            FStarC_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                          [uu___7] in
                        uu___5 :: uu___6 in
                      uu___3 :: uu___4 in
                    FStarC_Errors.log_issue
                      FStarC_Class_HasRange.hasRange_range rng
                      FStarC_Errors_Codes.Error_UninstantiatedUnificationVarInTactic
                      ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___2)
                | FStarC_TypeChecker_Rel.Implicit_checking_defers_univ_constraint
                    ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_Errors_Msg.text
                            "Tactic left uninstantiated unification variable:" in
                        let uu___5 =
                          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_uvar
                            (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStarC_Errors_Msg.text "Type:" in
                          let uu___7 =
                            let uu___8 =
                              FStarC_Syntax_Util.ctx_uvar_typ
                                imp.FStarC_TypeChecker_Common.imp_uvar in
                            FStarC_Class_PP.pp
                              FStarC_Syntax_Print.pretty_term uu___8 in
                          FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStarC_Errors_Msg.text "Reason:" in
                            let uu___9 =
                              let uu___10 =
                                FStarC_Pprint.doc_of_string
                                  imp.FStarC_TypeChecker_Common.imp_reason in
                              FStarC_Pprint.dquotes uu___10 in
                            FStarC_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                          [uu___7] in
                        uu___5 :: uu___6 in
                      uu___3 :: uu___4 in
                    FStarC_Errors.log_issue
                      FStarC_Class_HasRange.hasRange_range rng
                      FStarC_Errors_Codes.Error_UninstantiatedUnificationVarInTactic
                      ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___2)
                | FStarC_TypeChecker_Rel.Implicit_has_typing_guard (tm, ty)
                    ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_Errors_Msg.text "Tactic solved goal:" in
                        let uu___5 =
                          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_uvar
                            (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStarC_Errors_Msg.text "Type:" in
                          let uu___7 =
                            let uu___8 =
                              FStarC_Syntax_Util.ctx_uvar_typ
                                imp.FStarC_TypeChecker_Common.imp_uvar in
                            FStarC_Class_PP.pp
                              FStarC_Syntax_Print.pretty_term uu___8 in
                          FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              FStarC_Errors_Msg.text "To the term:" in
                            let uu___9 =
                              FStarC_Class_PP.pp
                                FStarC_Syntax_Print.pretty_term tm in
                            FStarC_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                          let uu___8 =
                            let uu___9 =
                              FStarC_Errors_Msg.text
                                "But it has a non-trivial typing guard. Use gather_or_solve_explicit_guards_for_resolved_goals to inspect and prove these goals" in
                            [uu___9] in
                          uu___7 :: uu___8 in
                        uu___5 :: uu___6 in
                      uu___3 :: uu___4 in
                    FStarC_Errors.log_issue
                      FStarC_Class_HasRange.hasRange_range rng
                      FStarC_Errors_Codes.Error_UninstantiatedUnificationVarInTactic
                      ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___2))) is;
      FStarC_Errors.stop_if_err ()
let run_unembedded_tactic_on_ps :
  'a 'b .
    FStarC_Compiler_Range_Type.range ->
      FStarC_Compiler_Range_Type.range ->
        Prims.bool ->
          'a ->
            ('a -> 'b FStarC_Tactics_Monad.tac) ->
              FStarC_Tactics_Types.proofstate ->
                (FStarC_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_call ->
    fun rng_goal ->
      fun background ->
        fun arg ->
          fun tau ->
            fun ps ->
              let ps1 =
                {
                  FStarC_Tactics_Types.main_context =
                    (let uu___ = ps.FStarC_Tactics_Types.main_context in
                     {
                       FStarC_TypeChecker_Env.solver =
                         (uu___.FStarC_TypeChecker_Env.solver);
                       FStarC_TypeChecker_Env.range =
                         (uu___.FStarC_TypeChecker_Env.range);
                       FStarC_TypeChecker_Env.curmodule =
                         (uu___.FStarC_TypeChecker_Env.curmodule);
                       FStarC_TypeChecker_Env.gamma =
                         (uu___.FStarC_TypeChecker_Env.gamma);
                       FStarC_TypeChecker_Env.gamma_sig =
                         (uu___.FStarC_TypeChecker_Env.gamma_sig);
                       FStarC_TypeChecker_Env.gamma_cache =
                         (uu___.FStarC_TypeChecker_Env.gamma_cache);
                       FStarC_TypeChecker_Env.modules =
                         (uu___.FStarC_TypeChecker_Env.modules);
                       FStarC_TypeChecker_Env.expected_typ =
                         (uu___.FStarC_TypeChecker_Env.expected_typ);
                       FStarC_TypeChecker_Env.sigtab =
                         (uu___.FStarC_TypeChecker_Env.sigtab);
                       FStarC_TypeChecker_Env.attrtab =
                         (uu___.FStarC_TypeChecker_Env.attrtab);
                       FStarC_TypeChecker_Env.instantiate_imp =
                         (uu___.FStarC_TypeChecker_Env.instantiate_imp);
                       FStarC_TypeChecker_Env.effects =
                         (uu___.FStarC_TypeChecker_Env.effects);
                       FStarC_TypeChecker_Env.generalize =
                         (uu___.FStarC_TypeChecker_Env.generalize);
                       FStarC_TypeChecker_Env.letrecs =
                         (uu___.FStarC_TypeChecker_Env.letrecs);
                       FStarC_TypeChecker_Env.top_level =
                         (uu___.FStarC_TypeChecker_Env.top_level);
                       FStarC_TypeChecker_Env.check_uvars =
                         (uu___.FStarC_TypeChecker_Env.check_uvars);
                       FStarC_TypeChecker_Env.use_eq_strict =
                         (uu___.FStarC_TypeChecker_Env.use_eq_strict);
                       FStarC_TypeChecker_Env.is_iface =
                         (uu___.FStarC_TypeChecker_Env.is_iface);
                       FStarC_TypeChecker_Env.admit =
                         (uu___.FStarC_TypeChecker_Env.admit);
                       FStarC_TypeChecker_Env.lax_universes =
                         (uu___.FStarC_TypeChecker_Env.lax_universes);
                       FStarC_TypeChecker_Env.phase1 =
                         (uu___.FStarC_TypeChecker_Env.phase1);
                       FStarC_TypeChecker_Env.failhard =
                         (uu___.FStarC_TypeChecker_Env.failhard);
                       FStarC_TypeChecker_Env.flychecking =
                         (uu___.FStarC_TypeChecker_Env.flychecking);
                       FStarC_TypeChecker_Env.uvar_subtyping =
                         (uu___.FStarC_TypeChecker_Env.uvar_subtyping);
                       FStarC_TypeChecker_Env.intactics = true;
                       FStarC_TypeChecker_Env.nocoerce =
                         (uu___.FStarC_TypeChecker_Env.nocoerce);
                       FStarC_TypeChecker_Env.tc_term =
                         (uu___.FStarC_TypeChecker_Env.tc_term);
                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (uu___.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.universe_of =
                         (uu___.FStarC_TypeChecker_Env.universe_of);
                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (uu___.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.teq_nosmt_force =
                         (uu___.FStarC_TypeChecker_Env.teq_nosmt_force);
                       FStarC_TypeChecker_Env.subtype_nosmt_force =
                         (uu___.FStarC_TypeChecker_Env.subtype_nosmt_force);
                       FStarC_TypeChecker_Env.qtbl_name_and_index =
                         (uu___.FStarC_TypeChecker_Env.qtbl_name_and_index);
                       FStarC_TypeChecker_Env.normalized_eff_names =
                         (uu___.FStarC_TypeChecker_Env.normalized_eff_names);
                       FStarC_TypeChecker_Env.fv_delta_depths =
                         (uu___.FStarC_TypeChecker_Env.fv_delta_depths);
                       FStarC_TypeChecker_Env.proof_ns =
                         (uu___.FStarC_TypeChecker_Env.proof_ns);
                       FStarC_TypeChecker_Env.synth_hook =
                         (uu___.FStarC_TypeChecker_Env.synth_hook);
                       FStarC_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                       FStarC_TypeChecker_Env.splice =
                         (uu___.FStarC_TypeChecker_Env.splice);
                       FStarC_TypeChecker_Env.mpreprocess =
                         (uu___.FStarC_TypeChecker_Env.mpreprocess);
                       FStarC_TypeChecker_Env.postprocess =
                         (uu___.FStarC_TypeChecker_Env.postprocess);
                       FStarC_TypeChecker_Env.identifier_info =
                         (uu___.FStarC_TypeChecker_Env.identifier_info);
                       FStarC_TypeChecker_Env.tc_hooks =
                         (uu___.FStarC_TypeChecker_Env.tc_hooks);
                       FStarC_TypeChecker_Env.dsenv =
                         (uu___.FStarC_TypeChecker_Env.dsenv);
                       FStarC_TypeChecker_Env.nbe =
                         (uu___.FStarC_TypeChecker_Env.nbe);
                       FStarC_TypeChecker_Env.strict_args_tab =
                         (uu___.FStarC_TypeChecker_Env.strict_args_tab);
                       FStarC_TypeChecker_Env.erasable_types_tab =
                         (uu___.FStarC_TypeChecker_Env.erasable_types_tab);
                       FStarC_TypeChecker_Env.enable_defer_to_tac =
                         (uu___.FStarC_TypeChecker_Env.enable_defer_to_tac);
                       FStarC_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                       FStarC_TypeChecker_Env.erase_erasable_args =
                         (uu___.FStarC_TypeChecker_Env.erase_erasable_args);
                       FStarC_TypeChecker_Env.core_check =
                         (uu___.FStarC_TypeChecker_Env.core_check);
                       FStarC_TypeChecker_Env.missing_decl =
                         (uu___.FStarC_TypeChecker_Env.missing_decl)
                     });
                  FStarC_Tactics_Types.all_implicits =
                    (ps.FStarC_Tactics_Types.all_implicits);
                  FStarC_Tactics_Types.goals =
                    (ps.FStarC_Tactics_Types.goals);
                  FStarC_Tactics_Types.smt_goals =
                    (ps.FStarC_Tactics_Types.smt_goals);
                  FStarC_Tactics_Types.depth =
                    (ps.FStarC_Tactics_Types.depth);
                  FStarC_Tactics_Types.__dump =
                    (ps.FStarC_Tactics_Types.__dump);
                  FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
                  FStarC_Tactics_Types.entry_range =
                    (ps.FStarC_Tactics_Types.entry_range);
                  FStarC_Tactics_Types.guard_policy =
                    (ps.FStarC_Tactics_Types.guard_policy);
                  FStarC_Tactics_Types.freshness =
                    (ps.FStarC_Tactics_Types.freshness);
                  FStarC_Tactics_Types.tac_verb_dbg =
                    (ps.FStarC_Tactics_Types.tac_verb_dbg);
                  FStarC_Tactics_Types.local_state =
                    (ps.FStarC_Tactics_Types.local_state);
                  FStarC_Tactics_Types.urgency =
                    (ps.FStarC_Tactics_Types.urgency);
                  FStarC_Tactics_Types.dump_on_failure =
                    (ps.FStarC_Tactics_Types.dump_on_failure)
                } in
              let ps2 =
                {
                  FStarC_Tactics_Types.main_context =
                    (let uu___ = ps1.FStarC_Tactics_Types.main_context in
                     {
                       FStarC_TypeChecker_Env.solver =
                         (uu___.FStarC_TypeChecker_Env.solver);
                       FStarC_TypeChecker_Env.range = rng_goal;
                       FStarC_TypeChecker_Env.curmodule =
                         (uu___.FStarC_TypeChecker_Env.curmodule);
                       FStarC_TypeChecker_Env.gamma =
                         (uu___.FStarC_TypeChecker_Env.gamma);
                       FStarC_TypeChecker_Env.gamma_sig =
                         (uu___.FStarC_TypeChecker_Env.gamma_sig);
                       FStarC_TypeChecker_Env.gamma_cache =
                         (uu___.FStarC_TypeChecker_Env.gamma_cache);
                       FStarC_TypeChecker_Env.modules =
                         (uu___.FStarC_TypeChecker_Env.modules);
                       FStarC_TypeChecker_Env.expected_typ =
                         (uu___.FStarC_TypeChecker_Env.expected_typ);
                       FStarC_TypeChecker_Env.sigtab =
                         (uu___.FStarC_TypeChecker_Env.sigtab);
                       FStarC_TypeChecker_Env.attrtab =
                         (uu___.FStarC_TypeChecker_Env.attrtab);
                       FStarC_TypeChecker_Env.instantiate_imp =
                         (uu___.FStarC_TypeChecker_Env.instantiate_imp);
                       FStarC_TypeChecker_Env.effects =
                         (uu___.FStarC_TypeChecker_Env.effects);
                       FStarC_TypeChecker_Env.generalize =
                         (uu___.FStarC_TypeChecker_Env.generalize);
                       FStarC_TypeChecker_Env.letrecs =
                         (uu___.FStarC_TypeChecker_Env.letrecs);
                       FStarC_TypeChecker_Env.top_level =
                         (uu___.FStarC_TypeChecker_Env.top_level);
                       FStarC_TypeChecker_Env.check_uvars =
                         (uu___.FStarC_TypeChecker_Env.check_uvars);
                       FStarC_TypeChecker_Env.use_eq_strict =
                         (uu___.FStarC_TypeChecker_Env.use_eq_strict);
                       FStarC_TypeChecker_Env.is_iface =
                         (uu___.FStarC_TypeChecker_Env.is_iface);
                       FStarC_TypeChecker_Env.admit =
                         (uu___.FStarC_TypeChecker_Env.admit);
                       FStarC_TypeChecker_Env.lax_universes =
                         (uu___.FStarC_TypeChecker_Env.lax_universes);
                       FStarC_TypeChecker_Env.phase1 =
                         (uu___.FStarC_TypeChecker_Env.phase1);
                       FStarC_TypeChecker_Env.failhard =
                         (uu___.FStarC_TypeChecker_Env.failhard);
                       FStarC_TypeChecker_Env.flychecking =
                         (uu___.FStarC_TypeChecker_Env.flychecking);
                       FStarC_TypeChecker_Env.uvar_subtyping =
                         (uu___.FStarC_TypeChecker_Env.uvar_subtyping);
                       FStarC_TypeChecker_Env.intactics =
                         (uu___.FStarC_TypeChecker_Env.intactics);
                       FStarC_TypeChecker_Env.nocoerce =
                         (uu___.FStarC_TypeChecker_Env.nocoerce);
                       FStarC_TypeChecker_Env.tc_term =
                         (uu___.FStarC_TypeChecker_Env.tc_term);
                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (uu___.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.universe_of =
                         (uu___.FStarC_TypeChecker_Env.universe_of);
                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (uu___.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.teq_nosmt_force =
                         (uu___.FStarC_TypeChecker_Env.teq_nosmt_force);
                       FStarC_TypeChecker_Env.subtype_nosmt_force =
                         (uu___.FStarC_TypeChecker_Env.subtype_nosmt_force);
                       FStarC_TypeChecker_Env.qtbl_name_and_index =
                         (uu___.FStarC_TypeChecker_Env.qtbl_name_and_index);
                       FStarC_TypeChecker_Env.normalized_eff_names =
                         (uu___.FStarC_TypeChecker_Env.normalized_eff_names);
                       FStarC_TypeChecker_Env.fv_delta_depths =
                         (uu___.FStarC_TypeChecker_Env.fv_delta_depths);
                       FStarC_TypeChecker_Env.proof_ns =
                         (uu___.FStarC_TypeChecker_Env.proof_ns);
                       FStarC_TypeChecker_Env.synth_hook =
                         (uu___.FStarC_TypeChecker_Env.synth_hook);
                       FStarC_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                       FStarC_TypeChecker_Env.splice =
                         (uu___.FStarC_TypeChecker_Env.splice);
                       FStarC_TypeChecker_Env.mpreprocess =
                         (uu___.FStarC_TypeChecker_Env.mpreprocess);
                       FStarC_TypeChecker_Env.postprocess =
                         (uu___.FStarC_TypeChecker_Env.postprocess);
                       FStarC_TypeChecker_Env.identifier_info =
                         (uu___.FStarC_TypeChecker_Env.identifier_info);
                       FStarC_TypeChecker_Env.tc_hooks =
                         (uu___.FStarC_TypeChecker_Env.tc_hooks);
                       FStarC_TypeChecker_Env.dsenv =
                         (uu___.FStarC_TypeChecker_Env.dsenv);
                       FStarC_TypeChecker_Env.nbe =
                         (uu___.FStarC_TypeChecker_Env.nbe);
                       FStarC_TypeChecker_Env.strict_args_tab =
                         (uu___.FStarC_TypeChecker_Env.strict_args_tab);
                       FStarC_TypeChecker_Env.erasable_types_tab =
                         (uu___.FStarC_TypeChecker_Env.erasable_types_tab);
                       FStarC_TypeChecker_Env.enable_defer_to_tac =
                         (uu___.FStarC_TypeChecker_Env.enable_defer_to_tac);
                       FStarC_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                       FStarC_TypeChecker_Env.erase_erasable_args =
                         (uu___.FStarC_TypeChecker_Env.erase_erasable_args);
                       FStarC_TypeChecker_Env.core_check =
                         (uu___.FStarC_TypeChecker_Env.core_check);
                       FStarC_TypeChecker_Env.missing_decl =
                         (uu___.FStarC_TypeChecker_Env.missing_decl)
                     });
                  FStarC_Tactics_Types.all_implicits =
                    (ps1.FStarC_Tactics_Types.all_implicits);
                  FStarC_Tactics_Types.goals =
                    (ps1.FStarC_Tactics_Types.goals);
                  FStarC_Tactics_Types.smt_goals =
                    (ps1.FStarC_Tactics_Types.smt_goals);
                  FStarC_Tactics_Types.depth =
                    (ps1.FStarC_Tactics_Types.depth);
                  FStarC_Tactics_Types.__dump =
                    (ps1.FStarC_Tactics_Types.__dump);
                  FStarC_Tactics_Types.psc = (ps1.FStarC_Tactics_Types.psc);
                  FStarC_Tactics_Types.entry_range =
                    (ps1.FStarC_Tactics_Types.entry_range);
                  FStarC_Tactics_Types.guard_policy =
                    (ps1.FStarC_Tactics_Types.guard_policy);
                  FStarC_Tactics_Types.freshness =
                    (ps1.FStarC_Tactics_Types.freshness);
                  FStarC_Tactics_Types.tac_verb_dbg =
                    (ps1.FStarC_Tactics_Types.tac_verb_dbg);
                  FStarC_Tactics_Types.local_state =
                    (ps1.FStarC_Tactics_Types.local_state);
                  FStarC_Tactics_Types.urgency =
                    (ps1.FStarC_Tactics_Types.urgency);
                  FStarC_Tactics_Types.dump_on_failure =
                    (ps1.FStarC_Tactics_Types.dump_on_failure)
                } in
              let env = ps2.FStarC_Tactics_Types.main_context in
              let res =
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      FStarC_TypeChecker_Env.current_module
                        ps2.FStarC_Tactics_Types.main_context in
                    FStarC_Ident.string_of_lid uu___2 in
                  FStar_Pervasives_Native.Some uu___1 in
                FStarC_Profiling.profile
                  (fun uu___1 ->
                     let uu___2 = tau arg in
                     FStarC_Tactics_Monad.run_safe uu___2 ps2) uu___
                  "FStarC.Tactics.Interpreter.run_safe" in
              (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Tac in
               if uu___1 then FStarC_Compiler_Util.print_string "}\n" else ());
              (match res with
               | FStarC_Tactics_Result.Success (ret, ps3) ->
                   ((let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Tac in
                     if uu___2
                     then
                       FStarC_Tactics_Printing.do_dump_proofstate ps3
                         "at the finish line"
                     else ());
                    (let remaining_smt_goals =
                       FStarC_Compiler_List.op_At
                         ps3.FStarC_Tactics_Types.goals
                         ps3.FStarC_Tactics_Types.smt_goals in
                     FStarC_Compiler_List.iter
                       (fun g ->
                          FStarC_Tactics_Monad.mark_goal_implicit_already_checked
                            g;
                          (let uu___4 = FStarC_Tactics_Monad.is_irrelevant g in
                           if uu___4
                           then
                             ((let uu___6 =
                                 FStarC_Compiler_Effect.op_Bang dbg_Tac in
                               if uu___6
                               then
                                 let uu___7 =
                                   let uu___8 =
                                     FStarC_Tactics_Types.goal_witness g in
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term uu___8 in
                                 FStarC_Compiler_Util.print1
                                   "Assigning irrelevant goal %s\n" uu___7
                               else ());
                              (let uu___6 =
                                 let uu___7 = FStarC_Tactics_Types.goal_env g in
                                 let uu___8 =
                                   FStarC_Tactics_Types.goal_witness g in
                                 FStarC_TypeChecker_Rel.teq_nosmt_force
                                   uu___7 uu___8 FStarC_Syntax_Util.exp_unit in
                               if uu___6
                               then ()
                               else
                                 (let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStarC_Tactics_Types.goal_witness g in
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term
                                        uu___10 in
                                    FStarC_Compiler_Util.format1
                                      "Irrelevant tactic witness does not unify with (): %s"
                                      uu___9 in
                                  failwith uu___8)))
                           else ())) remaining_smt_goals;
                     FStarC_Errors.with_ctx
                       "While checking implicits left by a tactic"
                       (fun uu___4 ->
                          (let uu___6 =
                             FStarC_Compiler_Effect.op_Bang dbg_Tac in
                           if uu___6
                           then
                             let uu___7 =
                               (FStarC_Common.string_of_list ())
                                 (fun imp ->
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_ctxu
                                      imp.FStarC_TypeChecker_Common.imp_uvar)
                                 ps3.FStarC_Tactics_Types.all_implicits in
                             FStarC_Compiler_Util.print1
                               "About to check tactic implicits: %s\n" uu___7
                           else ());
                          (let g =
                             let uu___6 =
                               FStarC_Class_Listlike.from_list
                                 (FStarC_Compiler_CList.listlike_clist ())
                                 ps3.FStarC_Tactics_Types.all_implicits in
                             {
                               FStarC_TypeChecker_Common.guard_f =
                                 (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.guard_f);
                               FStarC_TypeChecker_Common.deferred_to_tac =
                                 (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.deferred_to_tac);
                               FStarC_TypeChecker_Common.deferred =
                                 (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.deferred);
                               FStarC_TypeChecker_Common.univ_ineqs =
                                 (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.univ_ineqs);
                               FStarC_TypeChecker_Common.implicits = uu___6
                             } in
                           let g1 =
                             FStarC_TypeChecker_Rel.solve_deferred_constraints
                               env g in
                           (let uu___7 =
                              FStarC_Compiler_Effect.op_Bang dbg_Tac in
                            if uu___7
                            then
                              let uu___8 =
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_nat
                                  (FStarC_Compiler_List.length
                                     ps3.FStarC_Tactics_Types.all_implicits) in
                              let uu___9 =
                                FStarC_Class_Show.show
                                  (FStarC_Class_Show.show_list
                                     FStarC_TypeChecker_Common.showable_implicit)
                                  ps3.FStarC_Tactics_Types.all_implicits in
                              FStarC_Compiler_Util.print2
                                "Checked %s implicits (1): %s\n" uu___8
                                uu___9
                            else ());
                           (let tagged_implicits =
                              FStarC_TypeChecker_Rel.resolve_implicits_tac
                                env g1 in
                            (let uu___8 =
                               FStarC_Compiler_Effect.op_Bang dbg_Tac in
                             if uu___8
                             then
                               let uu___9 =
                                 FStarC_Class_Show.show
                                   FStarC_Class_Show.showable_nat
                                   (FStarC_Compiler_List.length
                                      ps3.FStarC_Tactics_Types.all_implicits) in
                               let uu___10 =
                                 FStarC_Class_Show.show
                                   (FStarC_Class_Show.show_list
                                      FStarC_TypeChecker_Common.showable_implicit)
                                   ps3.FStarC_Tactics_Types.all_implicits in
                               FStarC_Compiler_Util.print2
                                 "Checked %s implicits (2): %s\n" uu___9
                                 uu___10
                             else ());
                            report_implicits rng_goal tagged_implicits)));
                     (remaining_smt_goals, ret)))
               | FStarC_Tactics_Result.Failed
                   (FStarC_Errors.Error (code, msg, rng, ctx), ps3) ->
                   let msg1 =
                     let uu___1 = FStarC_Pprint.doc_of_string "Tactic failed" in
                     uu___1 :: msg in
                   FStarC_Compiler_Effect.raise
                     (FStarC_Errors.Error (code, msg1, rng, ctx))
               | FStarC_Tactics_Result.Failed (e, ps3) ->
                   (if ps3.FStarC_Tactics_Types.dump_on_failure
                    then
                      FStarC_Tactics_Printing.do_dump_proofstate ps3
                        "at the time of failure"
                    else ();
                    (let texn_to_doc e1 =
                       match e1 with
                       | FStarC_Tactics_Common.TacticFailure msg -> msg
                       | FStarC_Tactics_Common.EExn t ->
                           let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term t in
                                 Prims.strcat "Uncaught exception: " uu___5 in
                               FStarC_Pprint.doc_of_string uu___4 in
                             [uu___3] in
                           (uu___2, FStar_Pervasives_Native.None)
                       | e2 -> FStarC_Compiler_Effect.raise e2 in
                     let uu___2 = texn_to_doc e in
                     match uu___2 with
                     | (doc, rng) ->
                         let rng1 =
                           if background
                           then
                             match ps3.FStarC_Tactics_Types.goals with
                             | g::uu___3 ->
                                 (g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_range
                             | uu___3 -> rng_call
                           else
                             (match rng with
                              | FStar_Pervasives_Native.Some r -> r
                              | uu___4 ->
                                  ps3.FStarC_Tactics_Types.entry_range) in
                         let uu___3 =
                           let uu___4 =
                             if ps3.FStarC_Tactics_Types.dump_on_failure
                             then
                               let uu___5 =
                                 FStarC_Pprint.doc_of_string "Tactic failed" in
                               [uu___5]
                             else [] in
                           FStarC_Compiler_List.op_At uu___4 doc in
                         FStarC_Errors.raise_error
                           FStarC_Class_HasRange.hasRange_range rng1
                           FStarC_Errors_Codes.Fatal_UserTacticFailure ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_list_doc)
                           (Obj.magic uu___3))))
let run_tactic_on_ps' :
  'a 'b .
    FStarC_Compiler_Range_Type.range ->
      FStarC_Compiler_Range_Type.range ->
        Prims.bool ->
          'a FStarC_Syntax_Embeddings_Base.embedding ->
            'a ->
              'b FStarC_Syntax_Embeddings_Base.embedding ->
                FStarC_Syntax_Syntax.term ->
                  Prims.bool ->
                    FStarC_Tactics_Types.proofstate ->
                      (FStarC_Tactics_Types.goal Prims.list * 'b)
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
                    let env = ps.FStarC_Tactics_Types.main_context in
                    (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Tac in
                     if uu___1
                     then
                       let uu___2 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term tactic in
                       let uu___3 =
                         FStarC_Class_Show.show
                           FStarC_Class_Show.showable_bool
                           tactic_already_typed in
                       FStarC_Compiler_Util.print2
                         "Typechecking tactic: (%s) (already_typed: %s) {\n"
                         uu___2 uu___3
                     else ());
                    (let g =
                       if tactic_already_typed
                       then FStarC_TypeChecker_Env.trivial_guard
                       else
                         (let uu___2 =
                            let uu___3 =
                              FStarC_Syntax_Embeddings_Base.type_of e_arg in
                            let uu___4 =
                              FStarC_Syntax_Embeddings_Base.type_of e_res in
                            FStarC_TypeChecker_TcTerm.tc_tactic uu___3 uu___4
                              env tactic in
                          match uu___2 with | (uu___3, uu___4, g1) -> g1) in
                     (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Tac in
                      if uu___2
                      then FStarC_Compiler_Util.print_string "}\n"
                      else ());
                     FStarC_TypeChecker_Rel.force_trivial_guard env g;
                     FStarC_Errors.stop_if_err ();
                     (let tau =
                        unembed_tactic_1 e_arg e_res tactic
                          FStarC_Syntax_Embeddings_Base.id_norm_cb in
                      run_unembedded_tactic_on_ps rng_call rng_goal
                        background arg tau ps))
let run_tactic_on_ps :
  'a 'b .
    FStarC_Compiler_Range_Type.range ->
      FStarC_Compiler_Range_Type.range ->
        Prims.bool ->
          'a FStarC_Syntax_Embeddings_Base.embedding ->
            'a ->
              'b FStarC_Syntax_Embeddings_Base.embedding ->
                FStarC_Syntax_Syntax.term ->
                  Prims.bool ->
                    FStarC_Tactics_Types.proofstate ->
                      (FStarC_Tactics_Types.goal Prims.list * 'b)
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
                          FStarC_TypeChecker_Env.current_module
                            ps.FStarC_Tactics_Types.main_context in
                        FStarC_Ident.string_of_lid uu___2 in
                      FStar_Pervasives_Native.Some uu___1 in
                    FStarC_Profiling.profile
                      (fun uu___1 ->
                         run_tactic_on_ps' rng_call rng_goal background e_arg
                           arg e_res tactic tactic_already_typed ps) uu___
                      "FStarC.Tactics.Interpreter.run_tactic_on_ps"