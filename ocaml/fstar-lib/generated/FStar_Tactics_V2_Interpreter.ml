open Prims
let (tacdbg : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref false
let unembed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings_Base.norm_cb ->
          'uuuuu FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a -> fun norm_cb -> FStar_Syntax_Embeddings_Base.unembed ea a norm_cb
let embed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Compiler_Range_Type.range ->
        'uuuuu ->
          FStar_Syntax_Embeddings_Base.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu___ = FStar_Syntax_Embeddings_Base.embed ea x in
          uu___ r FStar_Pervasives_Native.None norm_cb
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu___ ->
    let step_from_native_step s =
      {
        FStar_TypeChecker_Cfg.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Cfg.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Cfg.univ_arity = Prims.int_zero;
        FStar_TypeChecker_Cfg.auto_reflect =
          (FStar_Pervasives_Native.Some
             (s.FStar_Tactics_Native.arity - Prims.int_one));
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution = false;
        FStar_TypeChecker_Cfg.interpretation =
          (fun psc ->
             fun cb ->
               fun _us -> fun t -> s.FStar_Tactics_Native.tactic psc cb t);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (fun _cb ->
             fun _us ->
               FStar_TypeChecker_NBETerm.dummy_interp
                 s.FStar_Tactics_Native.name)
      } in
    let uu___1 = FStar_Tactics_Native.list_all () in
    FStar_Compiler_List.map step_from_native_step uu___1
let mk_total_step_1' :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    Prims.int ->
      Prims.string ->
        ('uuuuu -> 'uuuuu1) ->
          'uuuuu FStar_Syntax_Embeddings_Base.embedding ->
            'uuuuu1 FStar_Syntax_Embeddings_Base.embedding ->
              ('uuuuu2 -> 'uuuuu3) ->
                'uuuuu2 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuu3 FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun er ->
            fun nf ->
              fun ena ->
                fun enr ->
                  let uu___ =
                    FStar_Tactics_V2_InterpFuns.mk_total_step_1 uarity nm f
                      ea er nf ena enr in
                  let uu___1 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu___1;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_1'_psc :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'uuuuu -> 'uuuuu1) ->
          'uuuuu FStar_Syntax_Embeddings_Base.embedding ->
            'uuuuu1 FStar_Syntax_Embeddings_Base.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'uuuuu2 -> 'uuuuu3) ->
                'uuuuu2 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuu3 FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun er ->
            fun nf ->
              fun ena ->
                fun enr ->
                  let uu___ =
                    FStar_Tactics_V2_InterpFuns.mk_total_step_1_psc uarity nm
                      f ea er nf ena enr in
                  let uu___1 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu___1;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_2' :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    Prims.int ->
      Prims.string ->
        ('uuuuu -> 'uuuuu1 -> 'uuuuu2) ->
          'uuuuu FStar_Syntax_Embeddings_Base.embedding ->
            'uuuuu1 FStar_Syntax_Embeddings_Base.embedding ->
              'uuuuu2 FStar_Syntax_Embeddings_Base.embedding ->
                ('uuuuu3 -> 'uuuuu4 -> 'uuuuu5) ->
                  'uuuuu3 FStar_TypeChecker_NBETerm.embedding ->
                    'uuuuu4 FStar_TypeChecker_NBETerm.embedding ->
                      'uuuuu5 FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun eb ->
            fun er ->
              fun nf ->
                fun ena ->
                  fun enb ->
                    fun enr ->
                      let uu___ =
                        FStar_Tactics_V2_InterpFuns.mk_total_step_2 uarity nm
                          f ea eb er nf ena enb enr in
                      let uu___1 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm) in
                      {
                        FStar_TypeChecker_Cfg.name = uu___1;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
let (__primitive_steps_ref :
  FStar_TypeChecker_Cfg.primitive_step Prims.list FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref []
let (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang __primitive_steps_ref in
    let uu___2 = native_tactics_steps () in
    FStar_Compiler_List.op_At uu___1 uu___2
let (register_tactic_primitive_step :
  FStar_TypeChecker_Cfg.primitive_step -> unit) =
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
  fun eb ->
    fun embedded_tac_b ->
      fun ncb ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos in
             let embedded_tac_b1 =
               FStar_Syntax_Util.mk_reify embedded_tac_b
                 (FStar_Pervasives_Native.Some
                    FStar_Parser_Const.effect_TAC_lid) in
             let tm =
               let uu___ =
                 let uu___1 =
                   let uu___2 =
                     embed FStar_Tactics_Embedding.e_proofstate rng
                       proof_state ncb in
                   FStar_Syntax_Syntax.as_arg uu___2 in
                 [uu___1] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu___ rng in
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
               let uu___ = FStar_Tactics_Embedding.e_result eb in
               unembed uu___ result ncb in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let h_result = t_head_of result in
                 let maybe_admit_tip =
                   let has_admit = FStar_Compiler_Util.mk_ref false in
                   let uu___ =
                     FStar_Syntax_Visit.visit_term
                       (fun t ->
                          match t.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.admit_lid
                              ->
                              (FStar_Compiler_Effect.op_Colon_Equals
                                 has_admit true;
                               FStar_Syntax_Syntax.tun)
                          | uu___1 -> FStar_Syntax_Syntax.tun) h_result in
                   let uu___1 = FStar_Compiler_Effect.op_Bang has_admit in
                   if uu___1
                   then
                     "\nThe term contains an `admit`, which will not reduce. Did you mean `tadmit()`?"
                   else "" in
                 let uu___ =
                   let uu___1 =
                     let uu___2 = FStar_Syntax_Print.term_to_string h_result in
                     FStar_Compiler_Util.format2
                       "Tactic got stuck!\nReduction stopped at: %s%s" uu___2
                       maybe_admit_tip in
                   (FStar_Errors_Codes.Fatal_TacticGotStuck, uu___1) in
                 FStar_Errors.raise_error uu___
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)
let unembed_tactic_nbe_0 :
  'b .
    'b FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'b FStar_Tactics_Monad.tac
  =
  fun eb ->
    fun cb ->
      fun embedded_tac_b ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state ->
             let result =
               let uu___ =
                 let uu___1 =
                   let uu___2 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state in
                   FStar_TypeChecker_NBETerm.as_arg uu___2 in
                 [uu___1] in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu___ in
             let res =
               let uu___ = FStar_Tactics_Embedding.e_result_nbe eb in
               FStar_TypeChecker_NBETerm.unembed uu___ cb result in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu___ =
                   let uu___1 =
                     let uu___2 =
                       FStar_TypeChecker_NBETerm.t_to_string result in
                     FStar_Compiler_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu___2 in
                   (FStar_Errors_Codes.Fatal_TacticGotStuck, uu___1) in
                 FStar_Errors.raise_error uu___
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)
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
             fun uu___4 -> failwith "Impossible: embedding tactic (thunk)?")
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
    let uu___ =
      FStar_TypeChecker_NBETerm.mk_t
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
    let uu___1 =
      FStar_Syntax_Embeddings_Base.emb_typ_of FStar_Syntax_Embeddings.e_unit in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb ->
         fun uu___2 -> failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb ->
         fun t ->
           let uu___2 =
             let uu___3 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t in
             uu___3 () in
           FStar_Pervasives_Native.Some uu___2) uu___ uu___1
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
               fun uu___4 -> failwith "Impossible: embedding tactic (1)?")
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
      let uu___ =
        FStar_TypeChecker_NBETerm.mk_t
          (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
      let uu___1 =
        FStar_Syntax_Embeddings_Base.emb_typ_of
          FStar_Syntax_Embeddings.e_unit in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb ->
           fun uu___2 -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb ->
           fun t ->
             let uu___2 = unembed_tactic_nbe_1 ea er cb t in
             FStar_Pervasives_Native.Some uu___2) uu___ uu___1
let unseal : 'uuuuu 'a . 'uuuuu -> 'a -> 'a FStar_Tactics_Monad.tac =
  fun _typ -> fun x -> FStar_Tactics_Monad.ret x
let (unseal_step : FStar_TypeChecker_Cfg.primitive_step) =
  let s =
    let uu___ =
      FStar_Syntax_Embeddings.e_sealed FStar_Syntax_Embeddings.e_any in
    let uu___1 =
      FStar_TypeChecker_NBETerm.e_sealed FStar_TypeChecker_NBETerm.e_any in
    FStar_Tactics_V2_InterpFuns.mk_tac_step_2 Prims.int_one "unseal" unseal
      FStar_Syntax_Embeddings.e_any uu___ FStar_Syntax_Embeddings.e_any
      unseal FStar_TypeChecker_NBETerm.e_any uu___1
      FStar_TypeChecker_NBETerm.e_any in
  {
    FStar_TypeChecker_Cfg.name = FStar_Parser_Const.unseal_lid;
    FStar_TypeChecker_Cfg.arity = (s.FStar_TypeChecker_Cfg.arity);
    FStar_TypeChecker_Cfg.univ_arity = (s.FStar_TypeChecker_Cfg.univ_arity);
    FStar_TypeChecker_Cfg.auto_reflect =
      (s.FStar_TypeChecker_Cfg.auto_reflect);
    FStar_TypeChecker_Cfg.strong_reduction_ok =
      (s.FStar_TypeChecker_Cfg.strong_reduction_ok);
    FStar_TypeChecker_Cfg.requires_binder_substitution =
      (s.FStar_TypeChecker_Cfg.requires_binder_substitution);
    FStar_TypeChecker_Cfg.interpretation =
      (s.FStar_TypeChecker_Cfg.interpretation);
    FStar_TypeChecker_Cfg.interpretation_nbe =
      (s.FStar_TypeChecker_Cfg.interpretation_nbe)
  }
let (uu___193 : unit) =
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_Tactics_V2_InterpFuns.mk_tac_step_1 Prims.int_zero "compress"
          FStar_Tactics_V2_Basic.compress
          FStar_Reflection_V2_Embeddings.e_term
          FStar_Reflection_V2_Embeddings.e_term
          FStar_Tactics_V2_Basic.compress
          FStar_Reflection_V2_NBEEmbeddings.e_term
          FStar_Reflection_V2_NBEEmbeddings.e_term in
      let uu___3 =
        let uu___4 =
          mk_total_step_1'_psc Prims.int_zero "tracepoint"
            FStar_Tactics_Types.tracepoint_with_psc
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_bool
            FStar_Tactics_Types.tracepoint_with_psc
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_bool in
        let uu___5 =
          let uu___6 =
            mk_total_step_2' Prims.int_zero "set_proofstate_range"
              FStar_Tactics_Types.set_proofstate_range
              FStar_Tactics_Embedding.e_proofstate
              FStar_Syntax_Embeddings.e_range
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.set_proofstate_range
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_TypeChecker_NBETerm.e_range
              FStar_Tactics_Embedding.e_proofstate_nbe in
          let uu___7 =
            let uu___8 =
              mk_total_step_1' Prims.int_zero "incr_depth"
                FStar_Tactics_Types.incr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.incr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe in
            let uu___9 =
              let uu___10 =
                mk_total_step_1' Prims.int_zero "decr_depth"
                  FStar_Tactics_Types.decr_depth
                  FStar_Tactics_Embedding.e_proofstate
                  FStar_Tactics_Embedding.e_proofstate
                  FStar_Tactics_Types.decr_depth
                  FStar_Tactics_Embedding.e_proofstate_nbe
                  FStar_Tactics_Embedding.e_proofstate_nbe in
              let uu___11 =
                let uu___12 =
                  let uu___13 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal in
                  let uu___14 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe in
                  mk_total_step_1' Prims.int_zero "goals_of"
                    FStar_Tactics_Types.goals_of
                    FStar_Tactics_Embedding.e_proofstate uu___13
                    FStar_Tactics_Types.goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu___14 in
                let uu___13 =
                  let uu___14 =
                    let uu___15 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Tactics_Embedding.e_goal in
                    let uu___16 =
                      FStar_TypeChecker_NBETerm.e_list
                        FStar_Tactics_Embedding.e_goal_nbe in
                    mk_total_step_1' Prims.int_zero "smt_goals_of"
                      FStar_Tactics_Types.smt_goals_of
                      FStar_Tactics_Embedding.e_proofstate uu___15
                      FStar_Tactics_Types.smt_goals_of
                      FStar_Tactics_Embedding.e_proofstate_nbe uu___16 in
                  let uu___15 =
                    let uu___16 =
                      mk_total_step_1' Prims.int_zero "goal_env"
                        FStar_Tactics_Types.goal_env
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_V2_Embeddings.e_env
                        FStar_Tactics_Types.goal_env
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_V2_NBEEmbeddings.e_env in
                    let uu___17 =
                      let uu___18 =
                        mk_total_step_1' Prims.int_zero "goal_type"
                          FStar_Tactics_Types.goal_type
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_V2_Embeddings.e_term
                          FStar_Tactics_Types.goal_type
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_V2_NBEEmbeddings.e_term in
                      let uu___19 =
                        let uu___20 =
                          mk_total_step_1' Prims.int_zero "goal_witness"
                            FStar_Tactics_Types.goal_witness
                            FStar_Tactics_Embedding.e_goal
                            FStar_Reflection_V2_Embeddings.e_term
                            FStar_Tactics_Types.goal_witness
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_Reflection_V2_NBEEmbeddings.e_term in
                        let uu___21 =
                          let uu___22 =
                            mk_total_step_1' Prims.int_zero "is_guard"
                              FStar_Tactics_Types.is_guard
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_bool
                              FStar_Tactics_Types.is_guard
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_bool in
                          let uu___23 =
                            let uu___24 =
                              mk_total_step_1' Prims.int_zero "get_label"
                                FStar_Tactics_Types.get_label
                                FStar_Tactics_Embedding.e_goal
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Types.get_label
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_TypeChecker_NBETerm.e_string in
                            let uu___25 =
                              let uu___26 =
                                mk_total_step_2' Prims.int_zero "set_label"
                                  FStar_Tactics_Types.set_label
                                  FStar_Syntax_Embeddings.e_string
                                  FStar_Tactics_Embedding.e_goal
                                  FStar_Tactics_Embedding.e_goal
                                  FStar_Tactics_Types.set_label
                                  FStar_TypeChecker_NBETerm.e_string
                                  FStar_Tactics_Embedding.e_goal_nbe
                                  FStar_Tactics_Embedding.e_goal_nbe in
                              let uu___27 =
                                let uu___28 =
                                  let uu___29 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal in
                                  let uu___30 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe in
                                  FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_goals"
                                    FStar_Tactics_Monad.set_goals uu___29
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_goals uu___30
                                    FStar_TypeChecker_NBETerm.e_unit in
                                let uu___29 =
                                  let uu___30 =
                                    let uu___31 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal in
                                    let uu___32 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe in
                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "set_smt_goals"
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu___31 FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu___32
                                      FStar_TypeChecker_NBETerm.e_unit in
                                  let uu___31 =
                                    let uu___32 =
                                      let uu___33 =
                                        e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu___34 =
                                        FStar_Syntax_Embeddings.e_either
                                          FStar_Tactics_Embedding.e_exn
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu___35 =
                                        e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any in
                                      let uu___36 =
                                        FStar_TypeChecker_NBETerm.e_either
                                          FStar_Tactics_Embedding.e_exn_nbe
                                          FStar_TypeChecker_NBETerm.e_any in
                                      FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                        Prims.int_one "catch"
                                        (fun uu___37 ->
                                           FStar_Tactics_Monad.catch)
                                        FStar_Syntax_Embeddings.e_any uu___33
                                        uu___34
                                        (fun uu___37 ->
                                           FStar_Tactics_Monad.catch)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu___35 uu___36 in
                                    let uu___33 =
                                      let uu___34 =
                                        let uu___35 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu___36 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu___37 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any in
                                        let uu___38 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any in
                                        FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                          Prims.int_one "recover"
                                          (fun uu___39 ->
                                             FStar_Tactics_Monad.recover)
                                          FStar_Syntax_Embeddings.e_any
                                          uu___35 uu___36
                                          (fun uu___39 ->
                                             FStar_Tactics_Monad.recover)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu___37 uu___38 in
                                      let uu___35 =
                                        let uu___36 =
                                          FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intro"
                                            FStar_Tactics_V2_Basic.intro
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Reflection_V2_Embeddings.e_binding
                                            FStar_Tactics_V2_Basic.intro
                                            FStar_TypeChecker_NBETerm.e_unit
                                            FStar_Reflection_V2_NBEEmbeddings.e_binding in
                                        let uu___37 =
                                          let uu___38 =
                                            let uu___39 =
                                              FStar_Syntax_Embeddings.e_tuple2
                                                FStar_Reflection_V2_Embeddings.e_binding
                                                FStar_Reflection_V2_Embeddings.e_binding in
                                            let uu___40 =
                                              FStar_TypeChecker_NBETerm.e_tuple2
                                                FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                FStar_Reflection_V2_NBEEmbeddings.e_binding in
                                            FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "intro_rec"
                                              FStar_Tactics_V2_Basic.intro_rec
                                              FStar_Syntax_Embeddings.e_unit
                                              uu___39
                                              FStar_Tactics_V2_Basic.intro_rec
                                              FStar_TypeChecker_NBETerm.e_unit
                                              uu___40 in
                                          let uu___39 =
                                            let uu___40 =
                                              let uu___41 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_norm_step in
                                              let uu___42 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_norm_step in
                                              FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                Prims.int_zero "norm"
                                                FStar_Tactics_V2_Basic.norm
                                                uu___41
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_V2_Basic.norm
                                                uu___42
                                                FStar_TypeChecker_NBETerm.e_unit in
                                            let uu___41 =
                                              let uu___42 =
                                                let uu___43 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step in
                                                let uu___44 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step in
                                                FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                  Prims.int_zero
                                                  "norm_term_env"
                                                  FStar_Tactics_V2_Basic.norm_term_env
                                                  FStar_Reflection_V2_Embeddings.e_env
                                                  uu___43
                                                  FStar_Reflection_V2_Embeddings.e_term
                                                  FStar_Reflection_V2_Embeddings.e_term
                                                  FStar_Tactics_V2_Basic.norm_term_env
                                                  FStar_Reflection_V2_NBEEmbeddings.e_env
                                                  uu___44
                                                  FStar_Reflection_V2_NBEEmbeddings.e_term
                                                  FStar_Reflection_V2_NBEEmbeddings.e_term in
                                              let uu___43 =
                                                let uu___44 =
                                                  let uu___45 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step in
                                                  let uu___46 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step in
                                                  FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                    Prims.int_zero
                                                    "norm_binding_type"
                                                    FStar_Tactics_V2_Basic.norm_binding_type
                                                    uu___45
                                                    FStar_Reflection_V2_Embeddings.e_binding
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_V2_Basic.norm_binding_type
                                                    uu___46
                                                    FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                let uu___45 =
                                                  let uu___46 =
                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                      Prims.int_zero
                                                      "rename_to"
                                                      FStar_Tactics_V2_Basic.rename_to
                                                      FStar_Reflection_V2_Embeddings.e_binding
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Reflection_V2_Embeddings.e_binding
                                                      FStar_Tactics_V2_Basic.rename_to
                                                      FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                      FStar_TypeChecker_NBETerm.e_string
                                                      FStar_Reflection_V2_NBEEmbeddings.e_binding in
                                                  let uu___47 =
                                                    let uu___48 =
                                                      FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "var_retype"
                                                        FStar_Tactics_V2_Basic.var_retype
                                                        FStar_Reflection_V2_Embeddings.e_binding
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_V2_Basic.var_retype
                                                        FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                        FStar_TypeChecker_NBETerm.e_unit in
                                                    let uu___49 =
                                                      let uu___50 =
                                                        FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "revert"
                                                          FStar_Tactics_V2_Basic.revert
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_V2_Basic.revert
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit in
                                                      let uu___51 =
                                                        let uu___52 =
                                                          FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "clear_top"
                                                            FStar_Tactics_V2_Basic.clear_top
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_V2_Basic.clear_top
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit in
                                                        let uu___53 =
                                                          let uu___54 =
                                                            FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "clear"
                                                              FStar_Tactics_V2_Basic.clear
                                                              FStar_Reflection_V2_Embeddings.e_binding
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_V2_Basic.clear
                                                              FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                              FStar_TypeChecker_NBETerm.e_unit in
                                                          let uu___55 =
                                                            let uu___56 =
                                                              FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "rewrite"
                                                                FStar_Tactics_V2_Basic.rewrite
                                                                FStar_Reflection_V2_Embeddings.e_binding
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_V2_Basic.rewrite
                                                                FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                                FStar_TypeChecker_NBETerm.e_unit in
                                                            let uu___57 =
                                                              let uu___58 =
                                                                FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                  Prims.int_zero
                                                                  "refine_intro"
                                                                  FStar_Tactics_V2_Basic.refine_intro
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_V2_Basic.refine_intro
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                  FStar_TypeChecker_NBETerm.e_unit in
                                                              let uu___59 =
                                                                let uu___60 =
                                                                  FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_exact"
                                                                    FStar_Tactics_V2_Basic.t_exact
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.t_exact
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                let uu___61 =
                                                                  let uu___62
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "t_apply"
                                                                    FStar_Tactics_V2_Basic.t_apply
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.t_apply
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                  let uu___63
                                                                    =
                                                                    let uu___64
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_apply_lemma"
                                                                    FStar_Tactics_V2_Basic.t_apply_lemma
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.t_apply_lemma
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_options"
                                                                    FStar_Tactics_V2_Basic.set_options
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.set_options
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tcc"
                                                                    FStar_Tactics_V2_Basic.tcc
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_comp
                                                                    FStar_Tactics_V2_Basic.tcc
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_comp in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tc"
                                                                    FStar_Tactics_V2_Basic.tc
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_V2_Basic.tc
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "unshelve"
                                                                    FStar_Tactics_V2_Basic.unshelve
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.unshelve
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_V2_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu___75
                                                                    ->
                                                                    fun
                                                                    uu___76
                                                                    ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "prune"
                                                                    FStar_Tactics_V2_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "addns"
                                                                    FStar_Tactics_V2_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "print"
                                                                    FStar_Tactics_V2_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "debugging"
                                                                    FStar_Tactics_V2_Basic.debugging
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_V2_Basic.debugging
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dump"
                                                                    FStar_Tactics_V2_Basic.dump
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.dump
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_all"
                                                                    FStar_Tactics_V2_Basic.dump_all
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.dump_all
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_uvars_of"
                                                                    FStar_Tactics_V2_Basic.dump_uvars_of
                                                                    FStar_Tactics_Embedding.e_goal
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.dump_uvars_of
                                                                    FStar_Tactics_Embedding.e_goal_nbe
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag in
                                                                    e_tactic_1
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___92 in
                                                                    let uu___92
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___94 in
                                                                    let uu___94
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu___91
                                                                    uu___92
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu___93
                                                                    uu___94
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_trefl"
                                                                    FStar_Tactics_V2_Basic.t_trefl
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.t_trefl
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStar_Tactics_V2_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    FStar_Tactics_V2_Basic.tadmit_t
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.tadmit_t
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStar_Tactics_V2_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu___102 in
                                                                    let uu___102
                                                                    =
                                                                    let uu___103
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu___103 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_V2_Basic.t_destruct
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___101
                                                                    FStar_Tactics_V2_Basic.t_destruct
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___102 in
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStar_Tactics_V2_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Tactics_V2_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env in
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "binder_bv"
                                                                    FStar_Tactics_V2_Basic.binder_bv
                                                                    FStar_Reflection_V2_Embeddings.e_binder
                                                                    FStar_Reflection_V2_Embeddings.e_bv
                                                                    FStar_Tactics_V2_Basic.binder_bv
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_binder
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_bv in
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStar_Tactics_V2_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_V2_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "curms"
                                                                    FStar_Tactics_V2_Basic.curms
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_V2_Basic.curms
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_V2_Embeddings.e_term in
                                                                    let uu___112
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_V2_Basic.uvar_env
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___111
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_V2_Basic.uvar_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    uu___112
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "ghost_uvar_env"
                                                                    FStar_Tactics_V2_Basic.ghost_uvar_env
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_V2_Basic.ghost_uvar_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh_universe_uvar"
                                                                    FStar_Tactics_V2_Basic.fresh_universe_uvar
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_V2_Basic.fresh_universe_uvar
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_env"
                                                                    FStar_Tactics_V2_Basic.unify_env
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_V2_Basic.unify_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_guard_env"
                                                                    FStar_Tactics_V2_Basic.unify_guard_env
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_V2_Basic.unify_guard_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "match_env"
                                                                    FStar_Tactics_V2_Basic.match_env
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_V2_Basic.match_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
                                                                    =
                                                                    let uu___123
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu___124
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_V2_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu___123
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_V2_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu___124
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_V2_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V2_Embeddings.e_bv
                                                                    FStar_Tactics_V2_Basic.fresh_bv_named
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_bv in
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    FStar_Tactics_V2_Basic.change
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.change
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_V2_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_V2_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe in
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_V2_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStar_Tactics_V2_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_V2_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_V2_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu___135
                                                                    ->
                                                                    fun
                                                                    uu___136
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "lset"
                                                                    FStar_Tactics_V2_Basic.lset
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (fun
                                                                    uu___137
                                                                    ->
                                                                    fun
                                                                    uu___138
                                                                    ->
                                                                    fun
                                                                    uu___139
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___137
                                                                    =
                                                                    let uu___138
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "set_urgency"
                                                                    FStar_Tactics_V2_Basic.set_urgency
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.set_urgency
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___139
                                                                    =
                                                                    let uu___140
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "t_commute_applied_match"
                                                                    FStar_Tactics_V2_Basic.t_commute_applied_match
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.t_commute_applied_match
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___141
                                                                    =
                                                                    let uu___142
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "gather_or_solve_explicit_guards_for_resolved_goals"
                                                                    FStar_Tactics_V2_Basic.gather_explicit_guards_for_resolved_goals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.gather_explicit_guards_for_resolved_goals
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___143
                                                                    =
                                                                    let uu___144
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "string_to_term"
                                                                    FStar_Tactics_V2_Basic.string_to_term
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_V2_Basic.string_to_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    let uu___145
                                                                    =
                                                                    let uu___146
                                                                    =
                                                                    let uu___147
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_binding in
                                                                    let uu___148
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_binding in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "push_bv_dsenv"
                                                                    FStar_Tactics_V2_Basic.push_bv_dsenv
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu___147
                                                                    FStar_Tactics_V2_Basic.push_bv_dsenv
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu___148 in
                                                                    let uu___147
                                                                    =
                                                                    let uu___148
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "term_to_string"
                                                                    FStar_Tactics_V2_Basic.term_to_string
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_V2_Basic.term_to_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu___149
                                                                    =
                                                                    let uu___150
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "comp_to_string"
                                                                    FStar_Tactics_V2_Basic.comp_to_string
                                                                    FStar_Reflection_V2_Embeddings.e_comp
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_V2_Basic.comp_to_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu___151
                                                                    =
                                                                    let uu___152
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "range_to_string"
                                                                    FStar_Tactics_V2_Basic.range_to_string
                                                                    FStar_Syntax_Embeddings.e_range
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_V2_Basic.range_to_string
                                                                    FStar_TypeChecker_NBETerm.e_range
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu___153
                                                                    =
                                                                    let uu___154
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "term_eq_old"
                                                                    FStar_Tactics_V2_Basic.term_eq_old
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_V2_Basic.term_eq_old
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu___155
                                                                    =
                                                                    let uu___156
                                                                    =
                                                                    let uu___157
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_any in
                                                                    let uu___158
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "with_compat_pre_core"
                                                                    (fun
                                                                    uu___159
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.with_compat_pre_core)
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    uu___157
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu___159
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.with_compat_pre_core)
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    uu___158
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu___157
                                                                    =
                                                                    let uu___158
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_vconfig"
                                                                    FStar_Tactics_V2_Basic.get_vconfig
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_Tactics_V2_Basic.get_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_vconfig in
                                                                    let uu___159
                                                                    =
                                                                    let uu___160
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_vconfig"
                                                                    FStar_Tactics_V2_Basic.set_vconfig
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.set_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___161
                                                                    =
                                                                    let uu___162
                                                                    =
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_smt_sync"
                                                                    FStar_Tactics_V2_Basic.t_smt_sync
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_V2_Basic.t_smt_sync
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___163
                                                                    =
                                                                    let uu___164
                                                                    =
                                                                    let uu___165
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    let uu___166
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "free_uvars"
                                                                    FStar_Tactics_V2_Basic.free_uvars
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___165
                                                                    FStar_Tactics_V2_Basic.free_uvars
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___166 in
                                                                    let uu___165
                                                                    =
                                                                    let uu___166
                                                                    =
                                                                    let uu___167
                                                                    =
                                                                    let uu___168
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___169
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___168
                                                                    uu___169 in
                                                                    let uu___168
                                                                    =
                                                                    let uu___169
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___170
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___169
                                                                    uu___170 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "check_subtyping"
                                                                    FStar_Tactics_V2_Basic.refl_check_subtyping
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___167
                                                                    FStar_Tactics_V2_Basic.refl_check_subtyping
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___168 in
                                                                    let uu___167
                                                                    =
                                                                    let uu___168
                                                                    =
                                                                    let uu___169
                                                                    =
                                                                    let uu___170
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___171
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___170
                                                                    uu___171 in
                                                                    let uu___170
                                                                    =
                                                                    let uu___171
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___172
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___171
                                                                    uu___172 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "check_equiv"
                                                                    FStar_Tactics_V2_Basic.refl_check_equiv
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___169
                                                                    FStar_Tactics_V2_Basic.refl_check_equiv
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___170 in
                                                                    let uu___169
                                                                    =
                                                                    let uu___170
                                                                    =
                                                                    let uu___171
                                                                    =
                                                                    let uu___172
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_V2_Embeddings.e_term in
                                                                    let uu___173
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___172
                                                                    uu___173 in
                                                                    let uu___172
                                                                    =
                                                                    let uu___173
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    let uu___174
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___173
                                                                    uu___174 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "core_compute_term_type"
                                                                    FStar_Tactics_V2_Basic.refl_core_compute_term_type
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost
                                                                    uu___171
                                                                    FStar_Tactics_V2_Basic.refl_core_compute_term_type
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    uu___172 in
                                                                    let uu___171
                                                                    =
                                                                    let uu___172
                                                                    =
                                                                    let uu___173
                                                                    =
                                                                    let uu___174
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___175
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___174
                                                                    uu___175 in
                                                                    let uu___174
                                                                    =
                                                                    let uu___175
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___176
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___175
                                                                    uu___176 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "core_check_term"
                                                                    FStar_Tactics_V2_Basic.refl_core_check_term
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost
                                                                    uu___173
                                                                    FStar_Tactics_V2_Basic.refl_core_check_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    uu___174 in
                                                                    let uu___173
                                                                    =
                                                                    let uu___174
                                                                    =
                                                                    let uu___175
                                                                    =
                                                                    let uu___176
                                                                    =
                                                                    let uu___177
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term in
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    uu___177 in
                                                                    let uu___177
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___176
                                                                    uu___177 in
                                                                    let uu___176
                                                                    =
                                                                    let uu___177
                                                                    =
                                                                    let uu___178
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    uu___178 in
                                                                    let uu___178
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___177
                                                                    uu___178 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "tc_term"
                                                                    FStar_Tactics_V2_Basic.refl_tc_term
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost
                                                                    uu___175
                                                                    FStar_Tactics_V2_Basic.refl_tc_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    uu___176 in
                                                                    let uu___175
                                                                    =
                                                                    let uu___176
                                                                    =
                                                                    let uu___177
                                                                    =
                                                                    let uu___178
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_V2_Embeddings.e_universe in
                                                                    let uu___179
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___178
                                                                    uu___179 in
                                                                    let uu___178
                                                                    =
                                                                    let uu___179
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_universe in
                                                                    let uu___180
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___179
                                                                    uu___180 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "universe_of"
                                                                    FStar_Tactics_V2_Basic.refl_universe_of
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___177
                                                                    FStar_Tactics_V2_Basic.refl_universe_of
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___178 in
                                                                    let uu___177
                                                                    =
                                                                    let uu___178
                                                                    =
                                                                    let uu___179
                                                                    =
                                                                    let uu___180
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___181
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___180
                                                                    uu___181 in
                                                                    let uu___180
                                                                    =
                                                                    let uu___181
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___182
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___181
                                                                    uu___182 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "check_prop_validity"
                                                                    FStar_Tactics_V2_Basic.refl_check_prop_validity
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___179
                                                                    FStar_Tactics_V2_Basic.refl_check_prop_validity
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___180 in
                                                                    let uu___179
                                                                    =
                                                                    let uu___180
                                                                    =
                                                                    let uu___181
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Reflection_V2_Embeddings.e_pattern in
                                                                    let uu___182
                                                                    =
                                                                    let uu___183
                                                                    =
                                                                    let uu___184
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Reflection_V2_Embeddings.e_pattern in
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Reflection_V2_Embeddings.e_binding in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu___186 in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___184
                                                                    uu___185 in
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    uu___183 in
                                                                    let uu___183
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_pattern in
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_pattern in
                                                                    let uu___187
                                                                    =
                                                                    let uu___188
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_binding in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu___188 in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___186
                                                                    uu___187 in
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    uu___185 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "check_match_complete"
                                                                    FStar_Tactics_V2_Basic.refl_check_match_complete
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___181
                                                                    uu___182
                                                                    FStar_Tactics_V2_Basic.refl_check_match_complete
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___183
                                                                    uu___184 in
                                                                    let uu___181
                                                                    =
                                                                    let uu___182
                                                                    =
                                                                    let uu___183
                                                                    =
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term in
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    uu___185 in
                                                                    let uu___185
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___184
                                                                    uu___185 in
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    uu___186 in
                                                                    let uu___186
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___185
                                                                    uu___186 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "instantiate_implicits"
                                                                    FStar_Tactics_V2_Basic.refl_instantiate_implicits
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___183
                                                                    FStar_Tactics_V2_Basic.refl_instantiate_implicits
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___184 in
                                                                    let uu___183
                                                                    =
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Tactics_Embedding.e_unfold_side in
                                                                    let uu___187
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___186
                                                                    uu___187 in
                                                                    let uu___186
                                                                    =
                                                                    let uu___187
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Tactics_Embedding.e_unfold_side_nbe in
                                                                    let uu___188
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___187
                                                                    uu___188 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "maybe_relate_after_unfolding"
                                                                    FStar_Tactics_V2_Basic.refl_maybe_relate_after_unfolding
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___185
                                                                    FStar_Tactics_V2_Basic.refl_maybe_relate_after_unfolding
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___186 in
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    let uu___187
                                                                    =
                                                                    let uu___188
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_V2_Embeddings.e_term in
                                                                    let uu___189
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___188
                                                                    uu___189 in
                                                                    let uu___188
                                                                    =
                                                                    let uu___189
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term in
                                                                    let uu___190
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    uu___189
                                                                    uu___190 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "maybe_unfold_head"
                                                                    FStar_Tactics_V2_Basic.refl_maybe_unfold_head
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    uu___187
                                                                    FStar_Tactics_V2_Basic.refl_maybe_unfold_head
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    uu___188 in
                                                                    let uu___187
                                                                    =
                                                                    let uu___188
                                                                    =
                                                                    let uu___189
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu___190
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "push_open_namespace"
                                                                    FStar_Tactics_V2_Basic.push_open_namespace
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___189
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Tactics_V2_Basic.push_open_namespace
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    uu___190
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env in
                                                                    let uu___189
                                                                    =
                                                                    let uu___190
                                                                    =
                                                                    let uu___191
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu___192
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "push_module_abbrev"
                                                                    FStar_Tactics_V2_Basic.push_module_abbrev
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu___191
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Tactics_V2_Basic.push_module_abbrev
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu___192
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env in
                                                                    let uu___191
                                                                    =
                                                                    let uu___192
                                                                    =
                                                                    let uu___194
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu___195
                                                                    =
                                                                    let uu___196
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_either
                                                                    FStar_Reflection_V2_Embeddings.e_bv
                                                                    FStar_Reflection_V2_Embeddings.e_fv in
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    uu___196 in
                                                                    let uu___196
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu___197
                                                                    =
                                                                    let uu___198
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_either
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_bv
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_fv in
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    uu___198 in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "resolve_name"
                                                                    FStar_Tactics_V2_Basic.resolve_name
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___194
                                                                    uu___195
                                                                    FStar_Tactics_V2_Basic.resolve_name
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    uu___196
                                                                    uu___197 in
                                                                    let uu___194
                                                                    =
                                                                    let uu___195
                                                                    =
                                                                    let uu___196
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue in
                                                                    let uu___197
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue in
                                                                    FStar_Tactics_V2_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "log_issues"
                                                                    (fun is
                                                                    ->
                                                                    FStar_Errors.add_issues
                                                                    is;
                                                                    FStar_Tactics_Monad.ret
                                                                    ())
                                                                    uu___196
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (fun is
                                                                    ->
                                                                    FStar_Errors.add_issues
                                                                    is;
                                                                    FStar_Tactics_Monad.ret
                                                                    ())
                                                                    uu___197
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    [uu___195] in
                                                                    uu___192
                                                                    ::
                                                                    uu___194 in
                                                                    uu___190
                                                                    ::
                                                                    uu___191 in
                                                                    uu___188
                                                                    ::
                                                                    uu___189 in
                                                                    uu___186
                                                                    ::
                                                                    uu___187 in
                                                                    uu___184
                                                                    ::
                                                                    uu___185 in
                                                                    uu___182
                                                                    ::
                                                                    uu___183 in
                                                                    uu___180
                                                                    ::
                                                                    uu___181 in
                                                                    uu___178
                                                                    ::
                                                                    uu___179 in
                                                                    uu___176
                                                                    ::
                                                                    uu___177 in
                                                                    uu___174
                                                                    ::
                                                                    uu___175 in
                                                                    uu___172
                                                                    ::
                                                                    uu___173 in
                                                                    uu___170
                                                                    ::
                                                                    uu___171 in
                                                                    uu___168
                                                                    ::
                                                                    uu___169 in
                                                                    uu___166
                                                                    ::
                                                                    uu___167 in
                                                                    uu___164
                                                                    ::
                                                                    uu___165 in
                                                                    uu___162
                                                                    ::
                                                                    uu___163 in
                                                                    uu___160
                                                                    ::
                                                                    uu___161 in
                                                                    uu___158
                                                                    ::
                                                                    uu___159 in
                                                                    uu___156
                                                                    ::
                                                                    uu___157 in
                                                                    uu___154
                                                                    ::
                                                                    uu___155 in
                                                                    uu___152
                                                                    ::
                                                                    uu___153 in
                                                                    uu___150
                                                                    ::
                                                                    uu___151 in
                                                                    uu___148
                                                                    ::
                                                                    uu___149 in
                                                                    uu___146
                                                                    ::
                                                                    uu___147 in
                                                                    uu___144
                                                                    ::
                                                                    uu___145 in
                                                                    uu___142
                                                                    ::
                                                                    uu___143 in
                                                                    uu___140
                                                                    ::
                                                                    uu___141 in
                                                                    uu___138
                                                                    ::
                                                                    uu___139 in
                                                                    uu___136
                                                                    ::
                                                                    uu___137 in
                                                                    uu___134
                                                                    ::
                                                                    uu___135 in
                                                                    uu___132
                                                                    ::
                                                                    uu___133 in
                                                                    uu___130
                                                                    ::
                                                                    uu___131 in
                                                                    uu___128
                                                                    ::
                                                                    uu___129 in
                                                                    uu___126
                                                                    ::
                                                                    uu___127 in
                                                                    uu___124
                                                                    ::
                                                                    uu___125 in
                                                                    uu___122
                                                                    ::
                                                                    uu___123 in
                                                                    uu___120
                                                                    ::
                                                                    uu___121 in
                                                                    uu___118
                                                                    ::
                                                                    uu___119 in
                                                                    uu___116
                                                                    ::
                                                                    uu___117 in
                                                                    uu___114
                                                                    ::
                                                                    uu___115 in
                                                                    uu___112
                                                                    ::
                                                                    uu___113 in
                                                                    uu___110
                                                                    ::
                                                                    uu___111 in
                                                                    uu___108
                                                                    ::
                                                                    uu___109 in
                                                                    uu___106
                                                                    ::
                                                                    uu___107 in
                                                                    uu___104
                                                                    ::
                                                                    uu___105 in
                                                                    uu___102
                                                                    ::
                                                                    uu___103 in
                                                                    uu___100
                                                                    ::
                                                                    uu___101 in
                                                                    uu___98
                                                                    ::
                                                                    uu___99 in
                                                                    uu___96
                                                                    ::
                                                                    uu___97 in
                                                                    uu___94
                                                                    ::
                                                                    uu___95 in
                                                                    uu___92
                                                                    ::
                                                                    uu___93 in
                                                                    uu___90
                                                                    ::
                                                                    uu___91 in
                                                                    uu___88
                                                                    ::
                                                                    uu___89 in
                                                                    uu___86
                                                                    ::
                                                                    uu___87 in
                                                                    uu___84
                                                                    ::
                                                                    uu___85 in
                                                                    uu___82
                                                                    ::
                                                                    uu___83 in
                                                                    uu___80
                                                                    ::
                                                                    uu___81 in
                                                                    uu___78
                                                                    ::
                                                                    uu___79 in
                                                                    uu___76
                                                                    ::
                                                                    uu___77 in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                    uu___64
                                                                    ::
                                                                    uu___65 in
                                                                  uu___62 ::
                                                                    uu___63 in
                                                                uu___60 ::
                                                                  uu___61 in
                                                              uu___58 ::
                                                                uu___59 in
                                                            uu___56 ::
                                                              uu___57 in
                                                          uu___54 :: uu___55 in
                                                        uu___52 :: uu___53 in
                                                      uu___50 :: uu___51 in
                                                    uu___48 :: uu___49 in
                                                  uu___46 :: uu___47 in
                                                uu___44 :: uu___45 in
                                              uu___42 :: uu___43 in
                                            uu___40 :: uu___41 in
                                          uu___38 :: uu___39 in
                                        uu___36 :: uu___37 in
                                      uu___34 :: uu___35 in
                                    uu___32 :: uu___33 in
                                  uu___30 :: uu___31 in
                                uu___28 :: uu___29 in
                              uu___26 :: uu___27 in
                            uu___24 :: uu___25 in
                          uu___22 :: uu___23 in
                        uu___20 :: uu___21 in
                      uu___18 :: uu___19 in
                    uu___16 :: uu___17 in
                  uu___14 :: uu___15 in
                uu___12 :: uu___13 in
              uu___10 :: uu___11 in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    unseal_step :: uu___1 in
  FStar_Compiler_List.iter register_tactic_primitive_step uu___
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
        failwith "Impossible: embedding tactic (1)?" in
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
      FStar_Compiler_Effect.op_Bar_Greater is
        (FStar_Compiler_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (imp, tag) ->
                  (match tag with
                   | FStar_TypeChecker_Rel.Implicit_unresolved ->
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStar_Syntax_Print.uvar_to_string
                               (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                           let uu___5 =
                             let uu___6 =
                               FStar_Syntax_Util.ctx_uvar_typ
                                 imp.FStar_TypeChecker_Common.imp_uvar in
                             FStar_Syntax_Print.term_to_string uu___6 in
                           FStar_Compiler_Util.format3
                             "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                             uu___4 uu___5
                             imp.FStar_TypeChecker_Common.imp_reason in
                         (FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic,
                           uu___3) in
                       FStar_Errors.log_issue rng uu___2
                   | FStar_TypeChecker_Rel.Implicit_checking_defers_univ_constraint
                       ->
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStar_Syntax_Print.uvar_to_string
                               (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                           let uu___5 =
                             let uu___6 =
                               FStar_Syntax_Util.ctx_uvar_typ
                                 imp.FStar_TypeChecker_Common.imp_uvar in
                             FStar_Syntax_Print.term_to_string uu___6 in
                           FStar_Compiler_Util.format3
                             "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                             uu___4 uu___5
                             imp.FStar_TypeChecker_Common.imp_reason in
                         (FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic,
                           uu___3) in
                       FStar_Errors.log_issue rng uu___2
                   | FStar_TypeChecker_Rel.Implicit_has_typing_guard 
                       (tm, ty) ->
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStar_Syntax_Print.uvar_to_string
                               (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                           let uu___5 =
                             let uu___6 =
                               FStar_Syntax_Util.ctx_uvar_typ
                                 imp.FStar_TypeChecker_Common.imp_uvar in
                             FStar_Syntax_Print.term_to_string uu___6 in
                           let uu___6 = FStar_Syntax_Print.term_to_string tm in
                           let uu___7 = FStar_Syntax_Print.term_to_string ty in
                           FStar_Compiler_Util.format4
                             "Tactic solved goal %s of type %s to %s : %s, but it has a non-trivial typing guard. Use gather_or_solve_explicit_guards_for_resolved_goals to inspect and prove these goals"
                             uu___4 uu___5 uu___6 uu___7 in
                         (FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic,
                           uu___3) in
                       FStar_Errors.log_issue rng uu___2)));
      FStar_Errors.stop_if_err ()
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
                        FStar_Tactics_Types.goals =
                          (ps.FStar_Tactics_Types.goals);
                        FStar_Tactics_Types.smt_goals =
                          (ps.FStar_Tactics_Types.smt_goals);
                        FStar_Tactics_Types.depth =
                          (ps.FStar_Tactics_Types.depth);
                        FStar_Tactics_Types.__dump =
                          (ps.FStar_Tactics_Types.__dump);
                        FStar_Tactics_Types.psc =
                          (ps.FStar_Tactics_Types.psc);
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
                          (ps.FStar_Tactics_Types.urgency)
                      } in
                    let env = ps1.FStar_Tactics_Types.main_context in
                    (let uu___1 = FStar_Compiler_Effect.op_Bang tacdbg in
                     if uu___1
                     then
                       let uu___2 = FStar_Syntax_Print.term_to_string tactic in
                       let uu___3 =
                         FStar_Compiler_Util.string_of_bool
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
                     (let uu___2 = FStar_Compiler_Effect.op_Bang tacdbg in
                      if uu___2
                      then FStar_Compiler_Util.print_string "}\n"
                      else ());
                     FStar_TypeChecker_Rel.force_trivial_guard env g;
                     FStar_Errors.stop_if_err ();
                     (let tau =
                        unembed_tactic_1 e_arg e_res tactic
                          FStar_Syntax_Embeddings_Base.id_norm_cb in
                      let res =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_TypeChecker_Env.current_module
                                ps1.FStar_Tactics_Types.main_context in
                            FStar_Ident.string_of_lid uu___6 in
                          FStar_Pervasives_Native.Some uu___5 in
                        FStar_Profiling.profile
                          (fun uu___5 ->
                             let uu___6 = tau arg in
                             FStar_Tactics_Monad.run_safe uu___6 ps1) uu___4
                          "FStar.Tactics.Interpreter.run_safe" in
                      (let uu___5 = FStar_Compiler_Effect.op_Bang tacdbg in
                       if uu___5
                       then FStar_Compiler_Util.print_string "}\n"
                       else ());
                      (match res with
                       | FStar_Tactics_Result.Success (ret, ps2) ->
                           let remaining_smt_goals =
                             FStar_Compiler_List.op_At
                               ps2.FStar_Tactics_Types.goals
                               ps2.FStar_Tactics_Types.smt_goals in
                           (FStar_Compiler_List.iter
                              (fun g1 ->
                                 FStar_Tactics_V2_Basic.mark_goal_implicit_already_checked
                                   g1;
                                 (let uu___7 =
                                    FStar_Tactics_Types.is_irrelevant g1 in
                                  if uu___7
                                  then
                                    ((let uu___9 =
                                        FStar_Compiler_Effect.op_Bang tacdbg in
                                      if uu___9
                                      then
                                        let uu___10 =
                                          let uu___11 =
                                            FStar_Tactics_Types.goal_witness
                                              g1 in
                                          FStar_Syntax_Print.term_to_string
                                            uu___11 in
                                        FStar_Compiler_Util.print1
                                          "Assigning irrelevant goal %s\n"
                                          uu___10
                                      else ());
                                     (let uu___9 =
                                        let uu___10 =
                                          FStar_Tactics_Types.goal_env g1 in
                                        let uu___11 =
                                          FStar_Tactics_Types.goal_witness g1 in
                                        FStar_TypeChecker_Rel.teq_nosmt_force
                                          uu___10 uu___11
                                          FStar_Syntax_Util.exp_unit in
                                      if uu___9
                                      then ()
                                      else
                                        (let uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               FStar_Tactics_Types.goal_witness
                                                 g1 in
                                             FStar_Syntax_Print.term_to_string
                                               uu___13 in
                                           FStar_Compiler_Util.format1
                                             "Irrelevant tactic witness does not unify with (): %s"
                                             uu___12 in
                                         failwith uu___11)))
                                  else ())) remaining_smt_goals;
                            (let uu___7 =
                               FStar_Compiler_Effect.op_Bang tacdbg in
                             if uu___7
                             then
                               let uu___8 =
                                 (FStar_Common.string_of_list ())
                                   (fun imp ->
                                      FStar_Syntax_Print.ctx_uvar_to_string
                                        imp.FStar_TypeChecker_Common.imp_uvar)
                                   ps2.FStar_Tactics_Types.all_implicits in
                               FStar_Compiler_Util.print1
                                 "About to check tactic implicits: %s\n"
                                 uu___8
                             else ());
                            (let g1 =
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
                                   (ps2.FStar_Tactics_Types.all_implicits)
                               } in
                             let g2 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env g1 in
                             (let uu___8 =
                                FStar_Compiler_Effect.op_Bang tacdbg in
                              if uu___8
                              then
                                let uu___9 =
                                  FStar_Compiler_Util.string_of_int
                                    (FStar_Compiler_List.length
                                       ps2.FStar_Tactics_Types.all_implicits) in
                                let uu___10 =
                                  (FStar_Common.string_of_list ())
                                    (fun imp ->
                                       FStar_Syntax_Print.ctx_uvar_to_string
                                         imp.FStar_TypeChecker_Common.imp_uvar)
                                    ps2.FStar_Tactics_Types.all_implicits in
                                FStar_Compiler_Util.print2
                                  "Checked %s implicits (1): %s\n" uu___9
                                  uu___10
                              else ());
                             (let tagged_implicits =
                                FStar_TypeChecker_Rel.resolve_implicits_tac
                                  env g2 in
                              (let uu___9 =
                                 FStar_Compiler_Effect.op_Bang tacdbg in
                               if uu___9
                               then
                                 let uu___10 =
                                   FStar_Compiler_Util.string_of_int
                                     (FStar_Compiler_List.length
                                        ps2.FStar_Tactics_Types.all_implicits) in
                                 let uu___11 =
                                   (FStar_Common.string_of_list ())
                                     (fun imp ->
                                        FStar_Syntax_Print.ctx_uvar_to_string
                                          imp.FStar_TypeChecker_Common.imp_uvar)
                                     ps2.FStar_Tactics_Types.all_implicits in
                                 FStar_Compiler_Util.print2
                                   "Checked %s implicits (2): %s\n" uu___10
                                   uu___11
                               else ());
                              report_implicits rng_goal tagged_implicits;
                              (let uu___11 =
                                 FStar_Compiler_Effect.op_Bang tacdbg in
                               if uu___11
                               then
                                 FStar_Tactics_Printing.do_dump_proofstate
                                   ps2 "at the finish line"
                               else ());
                              ((FStar_Compiler_List.op_At
                                  ps2.FStar_Tactics_Types.goals
                                  ps2.FStar_Tactics_Types.smt_goals), ret))))
                       | FStar_Tactics_Result.Failed (e, ps2) ->
                           (FStar_Tactics_Printing.do_dump_proofstate ps2
                              "at the time of failure";
                            (let texn_to_string e1 =
                               match e1 with
                               | FStar_Tactics_Common.TacticFailure s -> s
                               | FStar_Tactics_Common.EExn t ->
                                   let uu___6 =
                                     FStar_Syntax_Print.term_to_string t in
                                   Prims.op_Hat "uncaught exception: " uu___6
                               | e2 -> FStar_Compiler_Effect.raise e2 in
                             let rng =
                               if background
                               then
                                 match ps2.FStar_Tactics_Types.goals with
                                 | g1::uu___6 ->
                                     (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
                                 | uu___6 -> rng_call
                               else ps2.FStar_Tactics_Types.entry_range in
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 = texn_to_string e in
                                 FStar_Compiler_Util.format1
                                   "user tactic failed: `%s`" uu___8 in
                               (FStar_Errors_Codes.Fatal_UserTacticFailure,
                                 uu___7) in
                             FStar_Errors.raise_error uu___6 rng)))))
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