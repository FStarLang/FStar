open Prims
let solve : 'a . 'a -> 'a = fun ev -> ev
let embed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Compiler_Range_Type.range ->
        'a ->
          FStarC_Syntax_Embeddings_Base.norm_cb -> FStarC_Syntax_Syntax.term
  =
  fun e ->
    fun rng ->
      fun t ->
        fun n ->
          let uu___ = FStarC_Syntax_Embeddings_Base.embed e t in
          uu___ rng FStar_Pervasives_Native.None n
let unembed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Embeddings_Base.norm_cb ->
          'a FStar_Pervasives_Native.option
  = fun e -> fun t -> fun n -> FStarC_Syntax_Embeddings_Base.unembed e t n
let interp_ctx : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      FStarC_Errors.with_ctx (Prims.strcat "While running primitive " s) f
let run_wrap :
  'a .
    Prims.string ->
      'a FStarC_Tactics_Monad.tac ->
        FStarC_Tactics_Types.proofstate -> 'a FStarC_Tactics_Result.__result
  =
  fun label ->
    fun t ->
      fun ps ->
        interp_ctx label (fun uu___ -> FStarC_Tactics_Monad.run_safe t ps)
let (builtin_lid : Prims.string -> FStarC_Ident.lid) =
  fun nm ->
    FStarC_Parser_Const.fstar_stubs_tactics_lid' ["V2"; "Builtins"; nm]
let (types_lid : Prims.string -> FStarC_Ident.lid) =
  fun nm -> FStarC_Parser_Const.fstar_stubs_tactics_lid' ["Types"; nm]
let (set_auto_reflect :
  Prims.int ->
    FStarC_TypeChecker_Primops_Base.primitive_step ->
      FStarC_TypeChecker_Primops_Base.primitive_step)
  =
  fun arity ->
    fun p ->
      {
        FStarC_TypeChecker_Primops_Base.name =
          (p.FStarC_TypeChecker_Primops_Base.name);
        FStarC_TypeChecker_Primops_Base.arity =
          (p.FStarC_TypeChecker_Primops_Base.arity);
        FStarC_TypeChecker_Primops_Base.univ_arity =
          (p.FStarC_TypeChecker_Primops_Base.univ_arity);
        FStarC_TypeChecker_Primops_Base.auto_reflect =
          (FStar_Pervasives_Native.Some arity);
        FStarC_TypeChecker_Primops_Base.strong_reduction_ok =
          (p.FStarC_TypeChecker_Primops_Base.strong_reduction_ok);
        FStarC_TypeChecker_Primops_Base.requires_binder_substitution =
          (p.FStarC_TypeChecker_Primops_Base.requires_binder_substitution);
        FStarC_TypeChecker_Primops_Base.renorm_after =
          (p.FStarC_TypeChecker_Primops_Base.renorm_after);
        FStarC_TypeChecker_Primops_Base.interpretation =
          (p.FStarC_TypeChecker_Primops_Base.interpretation);
        FStarC_TypeChecker_Primops_Base.interpretation_nbe =
          (p.FStarC_TypeChecker_Primops_Base.interpretation_nbe)
      }
let mk_tot_step_1 :
  'nres 'nt1 'res 't1 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          'res FStarC_Syntax_Embeddings_Base.embedding ->
            'nt1 FStarC_TypeChecker_NBETerm.embedding ->
              'nres FStarC_TypeChecker_NBETerm.embedding ->
                ('t1 -> 'res) ->
                  ('nt1 -> 'nres) ->
                    FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun f ->
                fun nbe_f ->
                  let lid = types_lid nm in
                  FStarC_TypeChecker_Primops_Base.mk1' uarity lid uu___
                    uu___2 uu___1 uu___3
                    (fun x ->
                       let uu___4 = f x in
                       FStar_Pervasives_Native.Some uu___4)
                    (fun x ->
                       let uu___4 = nbe_f x in
                       FStar_Pervasives_Native.Some uu___4)
let mk_tot_step_2 :
  'nres 'nt1 'nt2 'res 't1 't2 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            'res FStarC_Syntax_Embeddings_Base.embedding ->
              'nt1 FStarC_TypeChecker_NBETerm.embedding ->
                'nt2 FStarC_TypeChecker_NBETerm.embedding ->
                  'nres FStarC_TypeChecker_NBETerm.embedding ->
                    ('t1 -> 't2 -> 'res) ->
                      ('nt1 -> 'nt2 -> 'nres) ->
                        FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun f ->
                    fun nbe_f ->
                      let lid = types_lid nm in
                      FStarC_TypeChecker_Primops_Base.mk2' uarity lid uu___
                        uu___3 uu___1 uu___4 uu___2 uu___5
                        (fun x ->
                           fun y ->
                             let uu___6 = f x y in
                             FStar_Pervasives_Native.Some uu___6)
                        (fun x ->
                           fun y ->
                             let uu___6 = nbe_f x y in
                             FStar_Pervasives_Native.Some uu___6)
let mk_tot_step_1_psc :
  'nres 'nt1 'res 't1 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          'res FStarC_Syntax_Embeddings_Base.embedding ->
            'nt1 FStarC_TypeChecker_NBETerm.embedding ->
              'nres FStarC_TypeChecker_NBETerm.embedding ->
                (FStarC_TypeChecker_Primops_Base.psc -> 't1 -> 'res) ->
                  (FStarC_TypeChecker_Primops_Base.psc -> 'nt1 -> 'nres) ->
                    FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun us ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun f ->
                fun nbe_f ->
                  let lid = types_lid nm in
                  FStarC_TypeChecker_Primops_Base.mk1_psc' us lid uu___
                    uu___2 uu___1 uu___3
                    (fun psc ->
                       fun x ->
                         let uu___4 = f psc x in
                         FStar_Pervasives_Native.Some uu___4)
                    (fun psc ->
                       fun x ->
                         let uu___4 = nbe_f psc x in
                         FStar_Pervasives_Native.Some uu___4)
let mk_tac_step_1 :
  'nres 'nt1 'res 't1 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          'res FStarC_Syntax_Embeddings_Base.embedding ->
            'nt1 FStarC_TypeChecker_NBETerm.embedding ->
              'nres FStarC_TypeChecker_NBETerm.embedding ->
                ('t1 -> 'res FStarC_Tactics_Monad.tac) ->
                  ('nt1 -> 'nres FStarC_Tactics_Monad.tac) ->
                    FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun univ_arity ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun f ->
                fun nbe_f ->
                  let lid = builtin_lid nm in
                  let uu___4 =
                    FStarC_TypeChecker_Primops_Base.mk2' univ_arity lid uu___
                      uu___2 FStarC_Tactics_Embedding.e_proofstate
                      FStarC_Tactics_Embedding.e_proofstate_nbe
                      (FStarC_Tactics_Embedding.e_result uu___1)
                      (FStarC_Tactics_Embedding.e_result_nbe uu___3)
                      (fun a ->
                         fun ps ->
                           let uu___5 =
                             let uu___6 = f a in run_wrap nm uu___6 ps in
                           FStar_Pervasives_Native.Some uu___5)
                      (fun a ->
                         fun ps ->
                           let uu___5 =
                             let uu___6 = nbe_f a in run_wrap nm uu___6 ps in
                           FStar_Pervasives_Native.Some uu___5) in
                  set_auto_reflect Prims.int_one uu___4
let mk_tac_step_2 :
  'nres 'nt1 'nt2 'res 't1 't2 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            'res FStarC_Syntax_Embeddings_Base.embedding ->
              'nt1 FStarC_TypeChecker_NBETerm.embedding ->
                'nt2 FStarC_TypeChecker_NBETerm.embedding ->
                  'nres FStarC_TypeChecker_NBETerm.embedding ->
                    ('t1 -> 't2 -> 'res FStarC_Tactics_Monad.tac) ->
                      ('nt1 -> 'nt2 -> 'nres FStarC_Tactics_Monad.tac) ->
                        FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun univ_arity ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun f ->
                    fun nbe_f ->
                      let lid = builtin_lid nm in
                      let uu___6 =
                        FStarC_TypeChecker_Primops_Base.mk3' univ_arity lid
                          uu___ uu___3 uu___1 uu___4
                          FStarC_Tactics_Embedding.e_proofstate
                          FStarC_Tactics_Embedding.e_proofstate_nbe
                          (FStarC_Tactics_Embedding.e_result uu___2)
                          (FStarC_Tactics_Embedding.e_result_nbe uu___5)
                          (fun a ->
                             fun b ->
                               fun ps ->
                                 let uu___7 =
                                   let uu___8 = f a b in
                                   run_wrap nm uu___8 ps in
                                 FStar_Pervasives_Native.Some uu___7)
                          (fun a ->
                             fun b ->
                               fun ps ->
                                 let uu___7 =
                                   let uu___8 = nbe_f a b in
                                   run_wrap nm uu___8 ps in
                                 FStar_Pervasives_Native.Some uu___7) in
                      set_auto_reflect (Prims.of_int (2)) uu___6
let mk_tac_step_3 :
  'nres 'nt1 'nt2 'nt3 'res 't1 't2 't3 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              'res FStarC_Syntax_Embeddings_Base.embedding ->
                'nt1 FStarC_TypeChecker_NBETerm.embedding ->
                  'nt2 FStarC_TypeChecker_NBETerm.embedding ->
                    'nt3 FStarC_TypeChecker_NBETerm.embedding ->
                      'nres FStarC_TypeChecker_NBETerm.embedding ->
                        ('t1 -> 't2 -> 't3 -> 'res FStarC_Tactics_Monad.tac)
                          ->
                          ('nt1 ->
                             'nt2 -> 'nt3 -> 'nres FStarC_Tactics_Monad.tac)
                            -> FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun univ_arity ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun f ->
                        fun nbe_f ->
                          let lid = builtin_lid nm in
                          let uu___8 =
                            FStarC_TypeChecker_Primops_Base.mk4' univ_arity
                              lid uu___ uu___4 uu___1 uu___5 uu___2 uu___6
                              FStarC_Tactics_Embedding.e_proofstate
                              FStarC_Tactics_Embedding.e_proofstate_nbe
                              (FStarC_Tactics_Embedding.e_result uu___3)
                              (FStarC_Tactics_Embedding.e_result_nbe uu___7)
                              (fun a ->
                                 fun b ->
                                   fun c ->
                                     fun ps ->
                                       let uu___9 =
                                         let uu___10 = f a b c in
                                         run_wrap nm uu___10 ps in
                                       FStar_Pervasives_Native.Some uu___9)
                              (fun a ->
                                 fun b ->
                                   fun c ->
                                     fun ps ->
                                       let uu___9 =
                                         let uu___10 = nbe_f a b c in
                                         run_wrap nm uu___10 ps in
                                       FStar_Pervasives_Native.Some uu___9) in
                          set_auto_reflect (Prims.of_int (3)) uu___8
let mk_tac_step_4 :
  'nres 'nt1 'nt2 'nt3 'nt4 'res 't1 't2 't3 't4 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                'res FStarC_Syntax_Embeddings_Base.embedding ->
                  'nt1 FStarC_TypeChecker_NBETerm.embedding ->
                    'nt2 FStarC_TypeChecker_NBETerm.embedding ->
                      'nt3 FStarC_TypeChecker_NBETerm.embedding ->
                        'nt4 FStarC_TypeChecker_NBETerm.embedding ->
                          'nres FStarC_TypeChecker_NBETerm.embedding ->
                            ('t1 ->
                               't2 ->
                                 't3 -> 't4 -> 'res FStarC_Tactics_Monad.tac)
                              ->
                              ('nt1 ->
                                 'nt2 ->
                                   'nt3 ->
                                     'nt4 -> 'nres FStarC_Tactics_Monad.tac)
                                ->
                                FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun univ_arity ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun uu___8 ->
                        fun uu___9 ->
                          fun f ->
                            fun nbe_f ->
                              let lid = builtin_lid nm in
                              let uu___10 =
                                FStarC_TypeChecker_Primops_Base.mk5'
                                  univ_arity lid uu___ uu___5 uu___1 uu___6
                                  uu___2 uu___7 uu___3 uu___8
                                  FStarC_Tactics_Embedding.e_proofstate
                                  FStarC_Tactics_Embedding.e_proofstate_nbe
                                  (FStarC_Tactics_Embedding.e_result uu___4)
                                  (FStarC_Tactics_Embedding.e_result_nbe
                                     uu___9)
                                  (fun a ->
                                     fun b ->
                                       fun c ->
                                         fun d ->
                                           fun ps ->
                                             let uu___11 =
                                               let uu___12 = f a b c d in
                                               run_wrap nm uu___12 ps in
                                             FStar_Pervasives_Native.Some
                                               uu___11)
                                  (fun a ->
                                     fun b ->
                                       fun c ->
                                         fun d ->
                                           fun ps ->
                                             let uu___11 =
                                               let uu___12 = nbe_f a b c d in
                                               run_wrap nm uu___12 ps in
                                             FStar_Pervasives_Native.Some
                                               uu___11) in
                              set_auto_reflect (Prims.of_int (4)) uu___10
let mk_tac_step_5 :
  'nres 'nt1 'nt2 'nt3 'nt4 'nt5 'res 't1 't2 't3 't4 't5 .
    Prims.int ->
      Prims.string ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  'res FStarC_Syntax_Embeddings_Base.embedding ->
                    'nt1 FStarC_TypeChecker_NBETerm.embedding ->
                      'nt2 FStarC_TypeChecker_NBETerm.embedding ->
                        'nt3 FStarC_TypeChecker_NBETerm.embedding ->
                          'nt4 FStarC_TypeChecker_NBETerm.embedding ->
                            'nt5 FStarC_TypeChecker_NBETerm.embedding ->
                              'nres FStarC_TypeChecker_NBETerm.embedding ->
                                ('t1 ->
                                   't2 ->
                                     't3 ->
                                       't4 ->
                                         't5 -> 'res FStarC_Tactics_Monad.tac)
                                  ->
                                  ('nt1 ->
                                     'nt2 ->
                                       'nt3 ->
                                         'nt4 ->
                                           'nt5 ->
                                             'nres FStarC_Tactics_Monad.tac)
                                    ->
                                    FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun univ_arity ->
    fun nm ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun uu___8 ->
                        fun uu___9 ->
                          fun uu___10 ->
                            fun uu___11 ->
                              fun f ->
                                fun nbe_f ->
                                  let lid = builtin_lid nm in
                                  let uu___12 =
                                    FStarC_TypeChecker_Primops_Base.mk6'
                                      univ_arity lid uu___ uu___6 uu___1
                                      uu___7 uu___2 uu___8 uu___3 uu___9
                                      uu___4 uu___10
                                      FStarC_Tactics_Embedding.e_proofstate
                                      FStarC_Tactics_Embedding.e_proofstate_nbe
                                      (FStarC_Tactics_Embedding.e_result
                                         uu___5)
                                      (FStarC_Tactics_Embedding.e_result_nbe
                                         uu___11)
                                      (fun a ->
                                         fun b ->
                                           fun c ->
                                             fun d ->
                                               fun e ->
                                                 fun ps ->
                                                   let uu___13 =
                                                     let uu___14 =
                                                       f a b c d e in
                                                     run_wrap nm uu___14 ps in
                                                   FStar_Pervasives_Native.Some
                                                     uu___13)
                                      (fun a ->
                                         fun b ->
                                           fun c ->
                                             fun d ->
                                               fun e ->
                                                 fun ps ->
                                                   let uu___13 =
                                                     let uu___14 =
                                                       nbe_f a b c d e in
                                                     run_wrap nm uu___14 ps in
                                                   FStar_Pervasives_Native.Some
                                                     uu___13) in
                                  set_auto_reflect (Prims.of_int (5)) uu___12
let (max_tac_arity : Prims.int) = (Prims.of_int (20))
let mk_tactic_interpretation_1 :
  'r 't1 .
    Prims.string ->
      ('t1 -> 'r FStarC_Tactics_Monad.tac) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          'r FStarC_Syntax_Embeddings_Base.embedding ->
            FStarC_TypeChecker_Primops_Base.psc ->
              FStarC_Syntax_Embeddings_Base.norm_cb ->
                FStarC_Syntax_Syntax.universes ->
                  FStarC_Syntax_Syntax.args ->
                    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun er ->
          fun psc ->
            fun ncb ->
              fun us ->
                fun args ->
                  match args with
                  | (a1, uu___)::(a2, uu___1)::[] ->
                      let uu___2 = unembed e1 a1 ncb in
                      FStarC_Compiler_Util.bind_opt uu___2
                        (fun a11 ->
                           let uu___3 =
                             unembed FStarC_Tactics_Embedding.e_proofstate a2
                               ncb in
                           FStarC_Compiler_Util.bind_opt uu___3
                             (fun ps ->
                                let ps1 =
                                  FStarC_Tactics_Types.set_ps_psc psc ps in
                                let r1 =
                                  interp_ctx name
                                    (fun uu___4 ->
                                       let uu___5 = t a11 in
                                       FStarC_Tactics_Monad.run_safe uu___5
                                         ps1) in
                                let uu___4 =
                                  let uu___5 =
                                    FStarC_TypeChecker_Primops_Base.psc_range
                                      psc in
                                  embed
                                    (FStarC_Tactics_Embedding.e_result er)
                                    uu___5 r1 ncb in
                                FStar_Pervasives_Native.Some uu___4))
                  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_2 :
  'r 't1 't2 .
    Prims.string ->
      ('t1 -> 't2 -> 'r FStarC_Tactics_Monad.tac) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            'r FStarC_Syntax_Embeddings_Base.embedding ->
              FStarC_TypeChecker_Primops_Base.psc ->
                FStarC_Syntax_Embeddings_Base.norm_cb ->
                  FStarC_Syntax_Syntax.universes ->
                    FStarC_Syntax_Syntax.args ->
                      FStarC_Syntax_Syntax.term
                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun er ->
            fun psc ->
              fun ncb ->
                fun us ->
                  fun args ->
                    match args with
                    | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
                        let uu___3 = unembed e1 a1 ncb in
                        FStarC_Compiler_Util.bind_opt uu___3
                          (fun a11 ->
                             let uu___4 = unembed e2 a2 ncb in
                             FStarC_Compiler_Util.bind_opt uu___4
                               (fun a21 ->
                                  let uu___5 =
                                    unembed
                                      FStarC_Tactics_Embedding.e_proofstate
                                      a3 ncb in
                                  FStarC_Compiler_Util.bind_opt uu___5
                                    (fun ps ->
                                       let ps1 =
                                         FStarC_Tactics_Types.set_ps_psc psc
                                           ps in
                                       let r1 =
                                         interp_ctx name
                                           (fun uu___6 ->
                                              let uu___7 = t a11 a21 in
                                              FStarC_Tactics_Monad.run_safe
                                                uu___7 ps1) in
                                       let uu___6 =
                                         let uu___7 =
                                           FStarC_TypeChecker_Primops_Base.psc_range
                                             psc in
                                         embed
                                           (FStarC_Tactics_Embedding.e_result
                                              er) uu___7 r1 ncb in
                                       FStar_Pervasives_Native.Some uu___6)))
                    | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_3 :
  'r 't1 't2 't3 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 'r FStarC_Tactics_Monad.tac) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              'r FStarC_Syntax_Embeddings_Base.embedding ->
                FStarC_TypeChecker_Primops_Base.psc ->
                  FStarC_Syntax_Embeddings_Base.norm_cb ->
                    FStarC_Syntax_Syntax.universes ->
                      FStarC_Syntax_Syntax.args ->
                        FStarC_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun er ->
              fun psc ->
                fun ncb ->
                  fun us ->
                    fun args ->
                      match args with
                      | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::[]
                          ->
                          let uu___4 = unembed e1 a1 ncb in
                          FStarC_Compiler_Util.bind_opt uu___4
                            (fun a11 ->
                               let uu___5 = unembed e2 a2 ncb in
                               FStarC_Compiler_Util.bind_opt uu___5
                                 (fun a21 ->
                                    let uu___6 = unembed e3 a3 ncb in
                                    FStarC_Compiler_Util.bind_opt uu___6
                                      (fun a31 ->
                                         let uu___7 =
                                           unembed
                                             FStarC_Tactics_Embedding.e_proofstate
                                             a4 ncb in
                                         FStarC_Compiler_Util.bind_opt uu___7
                                           (fun ps ->
                                              let ps1 =
                                                FStarC_Tactics_Types.set_ps_psc
                                                  psc ps in
                                              let r1 =
                                                interp_ctx name
                                                  (fun uu___8 ->
                                                     let uu___9 =
                                                       t a11 a21 a31 in
                                                     FStarC_Tactics_Monad.run_safe
                                                       uu___9 ps1) in
                                              let uu___8 =
                                                let uu___9 =
                                                  FStarC_TypeChecker_Primops_Base.psc_range
                                                    psc in
                                                embed
                                                  (FStarC_Tactics_Embedding.e_result
                                                     er) uu___9 r1 ncb in
                                              FStar_Pervasives_Native.Some
                                                uu___8))))
                      | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_4 :
  'r 't1 't2 't3 't4 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 'r FStarC_Tactics_Monad.tac) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                'r FStarC_Syntax_Embeddings_Base.embedding ->
                  FStarC_TypeChecker_Primops_Base.psc ->
                    FStarC_Syntax_Embeddings_Base.norm_cb ->
                      FStarC_Syntax_Syntax.universes ->
                        FStarC_Syntax_Syntax.args ->
                          FStarC_Syntax_Syntax.term
                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun er ->
                fun psc ->
                  fun ncb ->
                    fun us ->
                      fun args ->
                        match args with
                        | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4,
                                                                    uu___3)::
                            (a5, uu___4)::[] ->
                            let uu___5 = unembed e1 a1 ncb in
                            FStarC_Compiler_Util.bind_opt uu___5
                              (fun a11 ->
                                 let uu___6 = unembed e2 a2 ncb in
                                 FStarC_Compiler_Util.bind_opt uu___6
                                   (fun a21 ->
                                      let uu___7 = unembed e3 a3 ncb in
                                      FStarC_Compiler_Util.bind_opt uu___7
                                        (fun a31 ->
                                           let uu___8 = unembed e4 a4 ncb in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___8
                                             (fun a41 ->
                                                let uu___9 =
                                                  unembed
                                                    FStarC_Tactics_Embedding.e_proofstate
                                                    a5 ncb in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___9
                                                  (fun ps ->
                                                     let ps1 =
                                                       FStarC_Tactics_Types.set_ps_psc
                                                         psc ps in
                                                     let r1 =
                                                       interp_ctx name
                                                         (fun uu___10 ->
                                                            let uu___11 =
                                                              t a11 a21 a31
                                                                a41 in
                                                            FStarC_Tactics_Monad.run_safe
                                                              uu___11 ps1) in
                                                     let uu___10 =
                                                       let uu___11 =
                                                         FStarC_TypeChecker_Primops_Base.psc_range
                                                           psc in
                                                       embed
                                                         (FStarC_Tactics_Embedding.e_result
                                                            er) uu___11 r1
                                                         ncb in
                                                     FStar_Pervasives_Native.Some
                                                       uu___10)))))
                        | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r FStarC_Tactics_Monad.tac) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  'r FStarC_Syntax_Embeddings_Base.embedding ->
                    FStarC_TypeChecker_Primops_Base.psc ->
                      FStarC_Syntax_Embeddings_Base.norm_cb ->
                        FStarC_Syntax_Syntax.universes ->
                          FStarC_Syntax_Syntax.args ->
                            FStarC_Syntax_Syntax.term
                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun er ->
                  fun psc ->
                    fun ncb ->
                      fun us ->
                        fun args ->
                          match args with
                          | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                              (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::[] ->
                              let uu___6 = unembed e1 a1 ncb in
                              FStarC_Compiler_Util.bind_opt uu___6
                                (fun a11 ->
                                   let uu___7 = unembed e2 a2 ncb in
                                   FStarC_Compiler_Util.bind_opt uu___7
                                     (fun a21 ->
                                        let uu___8 = unembed e3 a3 ncb in
                                        FStarC_Compiler_Util.bind_opt uu___8
                                          (fun a31 ->
                                             let uu___9 = unembed e4 a4 ncb in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___9
                                               (fun a41 ->
                                                  let uu___10 =
                                                    unembed e5 a5 ncb in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___10
                                                    (fun a51 ->
                                                       let uu___11 =
                                                         unembed
                                                           FStarC_Tactics_Embedding.e_proofstate
                                                           a6 ncb in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___11
                                                         (fun ps ->
                                                            let ps1 =
                                                              FStarC_Tactics_Types.set_ps_psc
                                                                psc ps in
                                                            let r1 =
                                                              interp_ctx name
                                                                (fun uu___12
                                                                   ->
                                                                   let uu___13
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 in
                                                                   FStarC_Tactics_Monad.run_safe
                                                                    uu___13
                                                                    ps1) in
                                                            let uu___12 =
                                                              let uu___13 =
                                                                FStarC_TypeChecker_Primops_Base.psc_range
                                                                  psc in
                                                              embed
                                                                (FStarC_Tactics_Embedding.e_result
                                                                   er)
                                                                uu___13 r1
                                                                ncb in
                                                            FStar_Pervasives_Native.Some
                                                              uu___12))))))
                          | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    'r FStarC_Syntax_Embeddings_Base.embedding ->
                      FStarC_TypeChecker_Primops_Base.psc ->
                        FStarC_Syntax_Embeddings_Base.norm_cb ->
                          FStarC_Syntax_Syntax.universes ->
                            FStarC_Syntax_Syntax.args ->
                              FStarC_Syntax_Syntax.term
                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun er ->
                    fun psc ->
                      fun ncb ->
                        fun us ->
                          fun args ->
                            match args with
                            | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                (a7, uu___6)::[] ->
                                let uu___7 = unembed e1 a1 ncb in
                                FStarC_Compiler_Util.bind_opt uu___7
                                  (fun a11 ->
                                     let uu___8 = unembed e2 a2 ncb in
                                     FStarC_Compiler_Util.bind_opt uu___8
                                       (fun a21 ->
                                          let uu___9 = unembed e3 a3 ncb in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___9
                                            (fun a31 ->
                                               let uu___10 =
                                                 unembed e4 a4 ncb in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___10
                                                 (fun a41 ->
                                                    let uu___11 =
                                                      unembed e5 a5 ncb in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___11
                                                      (fun a51 ->
                                                         let uu___12 =
                                                           unembed e6 a6 ncb in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___12
                                                           (fun a61 ->
                                                              let uu___13 =
                                                                unembed
                                                                  FStarC_Tactics_Embedding.e_proofstate
                                                                  a7 ncb in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___13
                                                                (fun ps ->
                                                                   let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                   let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___15
                                                                    ps1) in
                                                                   let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___15
                                                                    r1 ncb in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu___14)))))))
                            | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      'r FStarC_Syntax_Embeddings_Base.embedding ->
                        FStarC_TypeChecker_Primops_Base.psc ->
                          FStarC_Syntax_Embeddings_Base.norm_cb ->
                            FStarC_Syntax_Syntax.universes ->
                              FStarC_Syntax_Syntax.args ->
                                FStarC_Syntax_Syntax.term
                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun er ->
                      fun psc ->
                        fun ncb ->
                          fun us ->
                            fun args ->
                              match args with
                              | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                  (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                  (a7, uu___6)::(a8, uu___7)::[] ->
                                  let uu___8 = unembed e1 a1 ncb in
                                  FStarC_Compiler_Util.bind_opt uu___8
                                    (fun a11 ->
                                       let uu___9 = unembed e2 a2 ncb in
                                       FStarC_Compiler_Util.bind_opt uu___9
                                         (fun a21 ->
                                            let uu___10 = unembed e3 a3 ncb in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___10
                                              (fun a31 ->
                                                 let uu___11 =
                                                   unembed e4 a4 ncb in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___11
                                                   (fun a41 ->
                                                      let uu___12 =
                                                        unembed e5 a5 ncb in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___12
                                                        (fun a51 ->
                                                           let uu___13 =
                                                             unembed e6 a6
                                                               ncb in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___13
                                                             (fun a61 ->
                                                                let uu___14 =
                                                                  unembed e7
                                                                    a7 ncb in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___14
                                                                  (fun a71 ->
                                                                    let uu___15
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___15
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___17
                                                                    ps1) in
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___17
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___16))))))))
                              | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        'r FStarC_Syntax_Embeddings_Base.embedding ->
                          FStarC_TypeChecker_Primops_Base.psc ->
                            FStarC_Syntax_Embeddings_Base.norm_cb ->
                              FStarC_Syntax_Syntax.universes ->
                                FStarC_Syntax_Syntax.args ->
                                  FStarC_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun er ->
                        fun psc ->
                          fun ncb ->
                            fun us ->
                              fun args ->
                                match args with
                                | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                    (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                    (a7, uu___6)::(a8, uu___7)::(a9, uu___8)::[]
                                    ->
                                    let uu___9 = unembed e1 a1 ncb in
                                    FStarC_Compiler_Util.bind_opt uu___9
                                      (fun a11 ->
                                         let uu___10 = unembed e2 a2 ncb in
                                         FStarC_Compiler_Util.bind_opt
                                           uu___10
                                           (fun a21 ->
                                              let uu___11 = unembed e3 a3 ncb in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___11
                                                (fun a31 ->
                                                   let uu___12 =
                                                     unembed e4 a4 ncb in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___12
                                                     (fun a41 ->
                                                        let uu___13 =
                                                          unembed e5 a5 ncb in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___13
                                                          (fun a51 ->
                                                             let uu___14 =
                                                               unembed e6 a6
                                                                 ncb in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___14
                                                               (fun a61 ->
                                                                  let uu___15
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___15
                                                                    (
                                                                    fun a71
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a81
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___19
                                                                    ps1) in
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___19
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___18)))))))))
                                | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          'r FStarC_Syntax_Embeddings_Base.embedding ->
                            FStarC_TypeChecker_Primops_Base.psc ->
                              FStarC_Syntax_Embeddings_Base.norm_cb ->
                                FStarC_Syntax_Syntax.universes ->
                                  FStarC_Syntax_Syntax.args ->
                                    FStarC_Syntax_Syntax.term
                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun er ->
                          fun psc ->
                            fun ncb ->
                              fun us ->
                                fun args ->
                                  match args with
                                  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                      (a4, uu___3)::(a5, uu___4)::(a6,
                                                                   uu___5)::
                                      (a7, uu___6)::(a8, uu___7)::(a9,
                                                                   uu___8)::
                                      (a10, uu___9)::[] ->
                                      let uu___10 = unembed e1 a1 ncb in
                                      FStarC_Compiler_Util.bind_opt uu___10
                                        (fun a11 ->
                                           let uu___11 = unembed e2 a2 ncb in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___11
                                             (fun a21 ->
                                                let uu___12 =
                                                  unembed e3 a3 ncb in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___12
                                                  (fun a31 ->
                                                     let uu___13 =
                                                       unembed e4 a4 ncb in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___13
                                                       (fun a41 ->
                                                          let uu___14 =
                                                            unembed e5 a5 ncb in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___14
                                                            (fun a51 ->
                                                               let uu___15 =
                                                                 unembed e6
                                                                   a6 ncb in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___15
                                                                 (fun a61 ->
                                                                    let uu___16
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a71
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a81
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a91
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a10 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___21
                                                                    ps1) in
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___21
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___20))))))))))
                                  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 -> 't8 -> 't9 -> 't10 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            'r FStarC_Syntax_Embeddings_Base.embedding ->
                              FStarC_TypeChecker_Primops_Base.psc ->
                                FStarC_Syntax_Embeddings_Base.norm_cb ->
                                  FStarC_Syntax_Syntax.universes ->
                                    FStarC_Syntax_Syntax.args ->
                                      FStarC_Syntax_Syntax.term
                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun er ->
                            fun psc ->
                              fun ncb ->
                                fun us ->
                                  fun args ->
                                    match args with
                                    | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                        (a4, uu___3)::(a5, uu___4)::(a6,
                                                                    uu___5)::
                                        (a7, uu___6)::(a8, uu___7)::(a9,
                                                                    uu___8)::
                                        (a10, uu___9)::(a11, uu___10)::[] ->
                                        let uu___11 = unembed e1 a1 ncb in
                                        FStarC_Compiler_Util.bind_opt uu___11
                                          (fun a12 ->
                                             let uu___12 = unembed e2 a2 ncb in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___12
                                               (fun a21 ->
                                                  let uu___13 =
                                                    unembed e3 a3 ncb in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___13
                                                    (fun a31 ->
                                                       let uu___14 =
                                                         unembed e4 a4 ncb in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___14
                                                         (fun a41 ->
                                                            let uu___15 =
                                                              unembed e5 a5
                                                                ncb in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___15
                                                              (fun a51 ->
                                                                 let uu___16
                                                                   =
                                                                   unembed e6
                                                                    a6 ncb in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___16
                                                                   (fun a61
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a71
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a81
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a91
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a101
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a11 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    t a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___23
                                                                    ps1) in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___23
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___22)))))))))))
                                    | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_11 :
  'r 't1 't10 't11 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 -> 't10 -> 't11 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              'r FStarC_Syntax_Embeddings_Base.embedding ->
                                FStarC_TypeChecker_Primops_Base.psc ->
                                  FStarC_Syntax_Embeddings_Base.norm_cb ->
                                    FStarC_Syntax_Syntax.universes ->
                                      FStarC_Syntax_Syntax.args ->
                                        FStarC_Syntax_Syntax.term
                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun er ->
                              fun psc ->
                                fun ncb ->
                                  fun us ->
                                    fun args ->
                                      match args with
                                      | (a1, uu___)::(a2, uu___1)::(a3,
                                                                    uu___2)::
                                          (a4, uu___3)::(a5, uu___4)::
                                          (a6, uu___5)::(a7, uu___6)::
                                          (a8, uu___7)::(a9, uu___8)::
                                          (a10, uu___9)::(a11, uu___10)::
                                          (a12, uu___11)::[] ->
                                          let uu___12 = unembed e1 a1 ncb in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___12
                                            (fun a13 ->
                                               let uu___13 =
                                                 unembed e2 a2 ncb in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___13
                                                 (fun a21 ->
                                                    let uu___14 =
                                                      unembed e3 a3 ncb in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___14
                                                      (fun a31 ->
                                                         let uu___15 =
                                                           unembed e4 a4 ncb in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___15
                                                           (fun a41 ->
                                                              let uu___16 =
                                                                unembed e5 a5
                                                                  ncb in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___16
                                                                (fun a51 ->
                                                                   let uu___17
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a61
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a71
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a81
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a91
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a101
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a111
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a12 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    t a13 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___25
                                                                    ps1) in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___25
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___24))))))))))))
                                      | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_12 :
  'r 't1 't10 't11 't12 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 -> 't11 -> 't12 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                'r FStarC_Syntax_Embeddings_Base.embedding ->
                                  FStarC_TypeChecker_Primops_Base.psc ->
                                    FStarC_Syntax_Embeddings_Base.norm_cb ->
                                      FStarC_Syntax_Syntax.universes ->
                                        FStarC_Syntax_Syntax.args ->
                                          FStarC_Syntax_Syntax.term
                                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun er ->
                                fun psc ->
                                  fun ncb ->
                                    fun us ->
                                      fun args ->
                                        match args with
                                        | (a1, uu___)::(a2, uu___1)::
                                            (a3, uu___2)::(a4, uu___3)::
                                            (a5, uu___4)::(a6, uu___5)::
                                            (a7, uu___6)::(a8, uu___7)::
                                            (a9, uu___8)::(a10, uu___9)::
                                            (a11, uu___10)::(a12, uu___11)::
                                            (a13, uu___12)::[] ->
                                            let uu___13 = unembed e1 a1 ncb in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___13
                                              (fun a14 ->
                                                 let uu___14 =
                                                   unembed e2 a2 ncb in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___14
                                                   (fun a21 ->
                                                      let uu___15 =
                                                        unembed e3 a3 ncb in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___15
                                                        (fun a31 ->
                                                           let uu___16 =
                                                             unembed e4 a4
                                                               ncb in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___16
                                                             (fun a41 ->
                                                                let uu___17 =
                                                                  unembed e5
                                                                    a5 ncb in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___17
                                                                  (fun a51 ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a61
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a71
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a81
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a91
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a101
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a111
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a121
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a13 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    t a14 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___27
                                                                    ps1) in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___27
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___26)))))))))))))
                                        | uu___ ->
                                            FStar_Pervasives_Native.None
let mk_tactic_interpretation_13 :
  'r 't1 't10 't11 't12 't13 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 -> 't13 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  'r FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    FStarC_TypeChecker_Primops_Base.psc ->
                                      FStarC_Syntax_Embeddings_Base.norm_cb
                                        ->
                                        FStarC_Syntax_Syntax.universes ->
                                          FStarC_Syntax_Syntax.args ->
                                            FStarC_Syntax_Syntax.term
                                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun er ->
                                  fun psc ->
                                    fun ncb ->
                                      fun us ->
                                        fun args ->
                                          match args with
                                          | (a1, uu___)::(a2, uu___1)::
                                              (a3, uu___2)::(a4, uu___3)::
                                              (a5, uu___4)::(a6, uu___5)::
                                              (a7, uu___6)::(a8, uu___7)::
                                              (a9, uu___8)::(a10, uu___9)::
                                              (a11, uu___10)::(a12, uu___11)::
                                              (a13, uu___12)::(a14, uu___13)::[]
                                              ->
                                              let uu___14 = unembed e1 a1 ncb in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___14
                                                (fun a15 ->
                                                   let uu___15 =
                                                     unembed e2 a2 ncb in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___15
                                                     (fun a21 ->
                                                        let uu___16 =
                                                          unembed e3 a3 ncb in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___16
                                                          (fun a31 ->
                                                             let uu___17 =
                                                               unembed e4 a4
                                                                 ncb in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___17
                                                               (fun a41 ->
                                                                  let uu___18
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (
                                                                    fun a51
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a61
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a71
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a81
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a91
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a101
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a111
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a121
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a14 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    t a15 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___29
                                                                    ps1) in
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___29
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___28))))))))))))))
                                          | uu___ ->
                                              FStar_Pervasives_Native.None
let mk_tactic_interpretation_14 :
  'r 't1 't10 't11 't12 't13 't14 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 -> 't14 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    'r
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      FStarC_TypeChecker_Primops_Base.psc ->
                                        FStarC_Syntax_Embeddings_Base.norm_cb
                                          ->
                                          FStarC_Syntax_Syntax.universes ->
                                            FStarC_Syntax_Syntax.args ->
                                              FStarC_Syntax_Syntax.term
                                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun er ->
                                    fun psc ->
                                      fun ncb ->
                                        fun us ->
                                          fun args ->
                                            match args with
                                            | (a1, uu___)::(a2, uu___1)::
                                                (a3, uu___2)::(a4, uu___3)::
                                                (a5, uu___4)::(a6, uu___5)::
                                                (a7, uu___6)::(a8, uu___7)::
                                                (a9, uu___8)::(a10, uu___9)::
                                                (a11, uu___10)::(a12,
                                                                 uu___11)::
                                                (a13, uu___12)::(a14,
                                                                 uu___13)::
                                                (a15, uu___14)::[] ->
                                                let uu___15 =
                                                  unembed e1 a1 ncb in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___15
                                                  (fun a16 ->
                                                     let uu___16 =
                                                       unembed e2 a2 ncb in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___16
                                                       (fun a21 ->
                                                          let uu___17 =
                                                            unembed e3 a3 ncb in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___17
                                                            (fun a31 ->
                                                               let uu___18 =
                                                                 unembed e4
                                                                   a4 ncb in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___18
                                                                 (fun a41 ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a51
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a61
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a71
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a81
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a91
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a101
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a111
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a121
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a15 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    t a16 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___31
                                                                    ps1) in
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___31
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___30)))))))))))))))
                                            | uu___ ->
                                                FStar_Pervasives_Native.None
let mk_tactic_interpretation_15 :
  'r 't1 't10 't11 't12 't13 't14 't15 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 -> 't15 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      'r
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        FStarC_TypeChecker_Primops_Base.psc
                                          ->
                                          FStarC_Syntax_Embeddings_Base.norm_cb
                                            ->
                                            FStarC_Syntax_Syntax.universes ->
                                              FStarC_Syntax_Syntax.args ->
                                                FStarC_Syntax_Syntax.term
                                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun er ->
                                      fun psc ->
                                        fun ncb ->
                                          fun us ->
                                            fun args ->
                                              match args with
                                              | (a1, uu___)::(a2, uu___1)::
                                                  (a3, uu___2)::(a4, uu___3)::
                                                  (a5, uu___4)::(a6, uu___5)::
                                                  (a7, uu___6)::(a8, uu___7)::
                                                  (a9, uu___8)::(a10, uu___9)::
                                                  (a11, uu___10)::(a12,
                                                                   uu___11)::
                                                  (a13, uu___12)::(a14,
                                                                   uu___13)::
                                                  (a15, uu___14)::(a16,
                                                                   uu___15)::[]
                                                  ->
                                                  let uu___16 =
                                                    unembed e1 a1 ncb in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___16
                                                    (fun a17 ->
                                                       let uu___17 =
                                                         unembed e2 a2 ncb in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___17
                                                         (fun a21 ->
                                                            let uu___18 =
                                                              unembed e3 a3
                                                                ncb in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___18
                                                              (fun a31 ->
                                                                 let uu___19
                                                                   =
                                                                   unembed e4
                                                                    a4 ncb in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___19
                                                                   (fun a41
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a51
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a61
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a71
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a81
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a91
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a101
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a111
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a121
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a16 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    t a17 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___33
                                                                    ps1) in
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___33
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___32))))))))))))))))
                                              | uu___ ->
                                                  FStar_Pervasives_Native.None
let mk_tactic_interpretation_16 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 ->
                                   't15 ->
                                     't16 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        'r
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          FStarC_TypeChecker_Primops_Base.psc
                                            ->
                                            FStarC_Syntax_Embeddings_Base.norm_cb
                                              ->
                                              FStarC_Syntax_Syntax.universes
                                                ->
                                                FStarC_Syntax_Syntax.args ->
                                                  FStarC_Syntax_Syntax.term
                                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun er ->
                                        fun psc ->
                                          fun ncb ->
                                            fun us ->
                                              fun args ->
                                                match args with
                                                | (a1, uu___)::(a2, uu___1)::
                                                    (a3, uu___2)::(a4,
                                                                   uu___3)::
                                                    (a5, uu___4)::(a6,
                                                                   uu___5)::
                                                    (a7, uu___6)::(a8,
                                                                   uu___7)::
                                                    (a9, uu___8)::(a10,
                                                                   uu___9)::
                                                    (a11, uu___10)::(a12,
                                                                    uu___11)::
                                                    (a13, uu___12)::(a14,
                                                                    uu___13)::
                                                    (a15, uu___14)::(a16,
                                                                    uu___15)::
                                                    (a17, uu___16)::[] ->
                                                    let uu___17 =
                                                      unembed e1 a1 ncb in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___17
                                                      (fun a18 ->
                                                         let uu___18 =
                                                           unembed e2 a2 ncb in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___18
                                                           (fun a21 ->
                                                              let uu___19 =
                                                                unembed e3 a3
                                                                  ncb in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___19
                                                                (fun a31 ->
                                                                   let uu___20
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a41
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a51
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a61
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a71
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a81
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a91
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a101
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a111
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a121
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a17 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    t a18 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___35
                                                                    ps1) in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___35
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___34)))))))))))))))))
                                                | uu___ ->
                                                    FStar_Pervasives_Native.None
let mk_tactic_interpretation_17 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't2 't3 't4 't5 't6 't7 't8
    't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 ->
                                   't15 ->
                                     't16 ->
                                       't17 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          'r
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            FStarC_TypeChecker_Primops_Base.psc
                                              ->
                                              FStarC_Syntax_Embeddings_Base.norm_cb
                                                ->
                                                FStarC_Syntax_Syntax.universes
                                                  ->
                                                  FStarC_Syntax_Syntax.args
                                                    ->
                                                    FStarC_Syntax_Syntax.term
                                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun er ->
                                          fun psc ->
                                            fun ncb ->
                                              fun us ->
                                                fun args ->
                                                  match args with
                                                  | (a1, uu___)::(a2, uu___1)::
                                                      (a3, uu___2)::(a4,
                                                                    uu___3)::
                                                      (a5, uu___4)::(a6,
                                                                    uu___5)::
                                                      (a7, uu___6)::(a8,
                                                                    uu___7)::
                                                      (a9, uu___8)::(a10,
                                                                    uu___9)::
                                                      (a11, uu___10)::
                                                      (a12, uu___11)::
                                                      (a13, uu___12)::
                                                      (a14, uu___13)::
                                                      (a15, uu___14)::
                                                      (a16, uu___15)::
                                                      (a17, uu___16)::
                                                      (a18, uu___17)::[] ->
                                                      let uu___18 =
                                                        unembed e1 a1 ncb in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___18
                                                        (fun a19 ->
                                                           let uu___19 =
                                                             unembed e2 a2
                                                               ncb in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___19
                                                             (fun a21 ->
                                                                let uu___20 =
                                                                  unembed e3
                                                                    a3 ncb in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___20
                                                                  (fun a31 ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a41
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a51
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a61
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a71
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a81
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a91
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a101
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a111
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a121
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a18 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    t a19 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161
                                                                    a171 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___37
                                                                    ps1) in
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___37
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___36))))))))))))))))))
                                                  | uu___ ->
                                                      FStar_Pervasives_Native.None
let mk_tactic_interpretation_18 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't2 't3 't4 't5 't6 't7
    't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 ->
                                   't15 ->
                                     't16 ->
                                       't17 ->
                                         't18 -> 'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          't18
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            'r
                                              FStarC_Syntax_Embeddings_Base.embedding
                                              ->
                                              FStarC_TypeChecker_Primops_Base.psc
                                                ->
                                                FStarC_Syntax_Embeddings_Base.norm_cb
                                                  ->
                                                  FStarC_Syntax_Syntax.universes
                                                    ->
                                                    FStarC_Syntax_Syntax.args
                                                      ->
                                                      FStarC_Syntax_Syntax.term
                                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun e18 ->
                                          fun er ->
                                            fun psc ->
                                              fun ncb ->
                                                fun us ->
                                                  fun args ->
                                                    match args with
                                                    | (a1, uu___)::(a2,
                                                                    uu___1)::
                                                        (a3, uu___2)::
                                                        (a4, uu___3)::
                                                        (a5, uu___4)::
                                                        (a6, uu___5)::
                                                        (a7, uu___6)::
                                                        (a8, uu___7)::
                                                        (a9, uu___8)::
                                                        (a10, uu___9)::
                                                        (a11, uu___10)::
                                                        (a12, uu___11)::
                                                        (a13, uu___12)::
                                                        (a14, uu___13)::
                                                        (a15, uu___14)::
                                                        (a16, uu___15)::
                                                        (a17, uu___16)::
                                                        (a18, uu___17)::
                                                        (a19, uu___18)::[] ->
                                                        let uu___19 =
                                                          unembed e1 a1 ncb in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___19
                                                          (fun a110 ->
                                                             let uu___20 =
                                                               unembed e2 a2
                                                                 ncb in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___20
                                                               (fun a21 ->
                                                                  let uu___21
                                                                    =
                                                                    unembed
                                                                    e3 a3 ncb in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (
                                                                    fun a31
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a41
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a51
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a61
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a71
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a81
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a91
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a101
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a111
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a121
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a19 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    t a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___39
                                                                    ps1) in
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___39
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___38)))))))))))))))))))
                                                    | uu___ ->
                                                        FStar_Pervasives_Native.None
let mk_tactic_interpretation_19 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't3 't4 't5
    't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 ->
                                   't15 ->
                                     't16 ->
                                       't17 ->
                                         't18 ->
                                           't19 ->
                                             'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          't18
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            't19
                                              FStarC_Syntax_Embeddings_Base.embedding
                                              ->
                                              'r
                                                FStarC_Syntax_Embeddings_Base.embedding
                                                ->
                                                FStarC_TypeChecker_Primops_Base.psc
                                                  ->
                                                  FStarC_Syntax_Embeddings_Base.norm_cb
                                                    ->
                                                    FStarC_Syntax_Syntax.universes
                                                      ->
                                                      FStarC_Syntax_Syntax.args
                                                        ->
                                                        FStarC_Syntax_Syntax.term
                                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun e18 ->
                                          fun e19 ->
                                            fun er ->
                                              fun psc ->
                                                fun ncb ->
                                                  fun us ->
                                                    fun args ->
                                                      match args with
                                                      | (a1, uu___)::
                                                          (a2, uu___1)::
                                                          (a3, uu___2)::
                                                          (a4, uu___3)::
                                                          (a5, uu___4)::
                                                          (a6, uu___5)::
                                                          (a7, uu___6)::
                                                          (a8, uu___7)::
                                                          (a9, uu___8)::
                                                          (a10, uu___9)::
                                                          (a11, uu___10)::
                                                          (a12, uu___11)::
                                                          (a13, uu___12)::
                                                          (a14, uu___13)::
                                                          (a15, uu___14)::
                                                          (a16, uu___15)::
                                                          (a17, uu___16)::
                                                          (a18, uu___17)::
                                                          (a19, uu___18)::
                                                          (a20, uu___19)::[]
                                                          ->
                                                          let uu___20 =
                                                            unembed e1 a1 ncb in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___20
                                                            (fun a110 ->
                                                               let uu___21 =
                                                                 unembed e2
                                                                   a2 ncb in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___21
                                                                 (fun a21 ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e3 a3 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a31
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a41
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a51
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a61
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a71
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a81
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a91
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a101
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a111
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a121
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a20 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___39
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    t a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___41
                                                                    ps1) in
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___41
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___40))))))))))))))))))))
                                                      | uu___ ->
                                                          FStar_Pervasives_Native.None
let mk_tactic_interpretation_20 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't20 't3 't4
    't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 ->
                                   't15 ->
                                     't16 ->
                                       't17 ->
                                         't18 ->
                                           't19 ->
                                             't20 ->
                                               'r FStarC_Tactics_Monad.tac)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          't18
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            't19
                                              FStarC_Syntax_Embeddings_Base.embedding
                                              ->
                                              't20
                                                FStarC_Syntax_Embeddings_Base.embedding
                                                ->
                                                'r
                                                  FStarC_Syntax_Embeddings_Base.embedding
                                                  ->
                                                  FStarC_TypeChecker_Primops_Base.psc
                                                    ->
                                                    FStarC_Syntax_Embeddings_Base.norm_cb
                                                      ->
                                                      FStarC_Syntax_Syntax.universes
                                                        ->
                                                        FStarC_Syntax_Syntax.args
                                                          ->
                                                          FStarC_Syntax_Syntax.term
                                                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun t ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun e18 ->
                                          fun e19 ->
                                            fun e20 ->
                                              fun er ->
                                                fun psc ->
                                                  fun ncb ->
                                                    fun us ->
                                                      fun args ->
                                                        match args with
                                                        | (a1, uu___)::
                                                            (a2, uu___1)::
                                                            (a3, uu___2)::
                                                            (a4, uu___3)::
                                                            (a5, uu___4)::
                                                            (a6, uu___5)::
                                                            (a7, uu___6)::
                                                            (a8, uu___7)::
                                                            (a9, uu___8)::
                                                            (a10, uu___9)::
                                                            (a11, uu___10)::
                                                            (a12, uu___11)::
                                                            (a13, uu___12)::
                                                            (a14, uu___13)::
                                                            (a15, uu___14)::
                                                            (a16, uu___15)::
                                                            (a17, uu___16)::
                                                            (a18, uu___17)::
                                                            (a19, uu___18)::
                                                            (a20, uu___19)::
                                                            (a21, uu___20)::[]
                                                            ->
                                                            let uu___21 =
                                                              unembed e1 a1
                                                                ncb in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___21
                                                              (fun a110 ->
                                                                 let uu___22
                                                                   =
                                                                   unembed e2
                                                                    a2 ncb in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___22
                                                                   (fun a22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e3 a3 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a31
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a41
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a51
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a61
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a71
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a81
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a91
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a101
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a111
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a121
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a131
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a141
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a151
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a161
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a171
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___38
                                                                    (fun a181
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___39
                                                                    (fun a191
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    unembed
                                                                    e20 a20
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___40
                                                                    (fun a201
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate
                                                                    a21 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___41
                                                                    (fun ps
                                                                    ->
                                                                    let ps1 =
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc ps in
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    t a110
                                                                    a22 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191
                                                                    a201 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___43
                                                                    ps1) in
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed
                                                                    (FStarC_Tactics_Embedding.e_result
                                                                    er)
                                                                    uu___43
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___42)))))))))))))))))))))
                                                        | uu___ ->
                                                            FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_1 :
  'r 't1 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 'r FStarC_Tactics_Monad.tac) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            'r FStarC_TypeChecker_NBETerm.embedding ->
              FStarC_Syntax_Syntax.universes ->
                FStarC_TypeChecker_NBETerm.args ->
                  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun er ->
            fun us ->
              fun args ->
                match args with
                | (a1, uu___)::(a2, uu___1)::[] ->
                    let uu___2 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                    FStarC_Compiler_Util.bind_opt uu___2
                      (fun a11 ->
                         let uu___3 =
                           FStarC_TypeChecker_NBETerm.unembed
                             FStarC_Tactics_Embedding.e_proofstate_nbe cb a2 in
                         FStarC_Compiler_Util.bind_opt uu___3
                           (fun ps ->
                              let r1 =
                                interp_ctx name
                                  (fun uu___4 ->
                                     let uu___5 = t a11 in
                                     FStarC_Tactics_Monad.run_safe uu___5 ps) in
                              let uu___4 =
                                FStarC_TypeChecker_NBETerm.embed
                                  (FStarC_Tactics_Embedding.e_result_nbe er)
                                  cb r1 in
                              FStar_Pervasives_Native.Some uu___4))
                | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_2 :
  'r 't1 't2 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 'r FStarC_Tactics_Monad.tac) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              'r FStarC_TypeChecker_NBETerm.embedding ->
                FStarC_Syntax_Syntax.universes ->
                  FStarC_TypeChecker_NBETerm.args ->
                    FStarC_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun er ->
              fun us ->
                fun args ->
                  match args with
                  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
                      let uu___3 =
                        FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                      FStarC_Compiler_Util.bind_opt uu___3
                        (fun a11 ->
                           let uu___4 =
                             FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
                           FStarC_Compiler_Util.bind_opt uu___4
                             (fun a21 ->
                                let uu___5 =
                                  FStarC_TypeChecker_NBETerm.unembed
                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                    cb a3 in
                                FStarC_Compiler_Util.bind_opt uu___5
                                  (fun ps ->
                                     let r1 =
                                       interp_ctx name
                                         (fun uu___6 ->
                                            let uu___7 = t a11 a21 in
                                            FStarC_Tactics_Monad.run_safe
                                              uu___7 ps) in
                                     let uu___6 =
                                       FStarC_TypeChecker_NBETerm.embed
                                         (FStarC_Tactics_Embedding.e_result_nbe
                                            er) cb r1 in
                                     FStar_Pervasives_Native.Some uu___6)))
                  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_3 :
  'r 't1 't2 't3 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 'r FStarC_Tactics_Monad.tac) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                'r FStarC_TypeChecker_NBETerm.embedding ->
                  FStarC_Syntax_Syntax.universes ->
                    FStarC_TypeChecker_NBETerm.args ->
                      FStarC_TypeChecker_NBETerm.t
                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun er ->
                fun us ->
                  fun args ->
                    match args with
                    | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::[]
                        ->
                        let uu___4 =
                          FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                        FStarC_Compiler_Util.bind_opt uu___4
                          (fun a11 ->
                             let uu___5 =
                               FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
                             FStarC_Compiler_Util.bind_opt uu___5
                               (fun a21 ->
                                  let uu___6 =
                                    FStarC_TypeChecker_NBETerm.unembed e3 cb
                                      a3 in
                                  FStarC_Compiler_Util.bind_opt uu___6
                                    (fun a31 ->
                                       let uu___7 =
                                         FStarC_TypeChecker_NBETerm.unembed
                                           FStarC_Tactics_Embedding.e_proofstate_nbe
                                           cb a4 in
                                       FStarC_Compiler_Util.bind_opt uu___7
                                         (fun ps ->
                                            let r1 =
                                              interp_ctx name
                                                (fun uu___8 ->
                                                   let uu___9 = t a11 a21 a31 in
                                                   FStarC_Tactics_Monad.run_safe
                                                     uu___9 ps) in
                                            let uu___8 =
                                              FStarC_TypeChecker_NBETerm.embed
                                                (FStarC_Tactics_Embedding.e_result_nbe
                                                   er) cb r1 in
                                            FStar_Pervasives_Native.Some
                                              uu___8))))
                    | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_4 :
  'r 't1 't2 't3 't4 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 'r FStarC_Tactics_Monad.tac) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  'r FStarC_TypeChecker_NBETerm.embedding ->
                    FStarC_Syntax_Syntax.universes ->
                      FStarC_TypeChecker_NBETerm.args ->
                        FStarC_TypeChecker_NBETerm.t
                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun er ->
                  fun us ->
                    fun args ->
                      match args with
                      | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::
                          (a5, uu___4)::[] ->
                          let uu___5 =
                            FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                          FStarC_Compiler_Util.bind_opt uu___5
                            (fun a11 ->
                               let uu___6 =
                                 FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
                               FStarC_Compiler_Util.bind_opt uu___6
                                 (fun a21 ->
                                    let uu___7 =
                                      FStarC_TypeChecker_NBETerm.unembed e3
                                        cb a3 in
                                    FStarC_Compiler_Util.bind_opt uu___7
                                      (fun a31 ->
                                         let uu___8 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e4 cb a4 in
                                         FStarC_Compiler_Util.bind_opt uu___8
                                           (fun a41 ->
                                              let uu___9 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  FStarC_Tactics_Embedding.e_proofstate_nbe
                                                  cb a5 in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___9
                                                (fun ps ->
                                                   let r1 =
                                                     interp_ctx name
                                                       (fun uu___10 ->
                                                          let uu___11 =
                                                            t a11 a21 a31 a41 in
                                                          FStarC_Tactics_Monad.run_safe
                                                            uu___11 ps) in
                                                   let uu___10 =
                                                     FStarC_TypeChecker_NBETerm.embed
                                                       (FStarC_Tactics_Embedding.e_result_nbe
                                                          er) cb r1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu___10)))))
                      | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r FStarC_Tactics_Monad.tac) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    'r FStarC_TypeChecker_NBETerm.embedding ->
                      FStarC_Syntax_Syntax.universes ->
                        FStarC_TypeChecker_NBETerm.args ->
                          FStarC_TypeChecker_NBETerm.t
                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun er ->
                    fun us ->
                      fun args ->
                        match args with
                        | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4,
                                                                    uu___3)::
                            (a5, uu___4)::(a6, uu___5)::[] ->
                            let uu___6 =
                              FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                            FStarC_Compiler_Util.bind_opt uu___6
                              (fun a11 ->
                                 let uu___7 =
                                   FStarC_TypeChecker_NBETerm.unembed e2 cb
                                     a2 in
                                 FStarC_Compiler_Util.bind_opt uu___7
                                   (fun a21 ->
                                      let uu___8 =
                                        FStarC_TypeChecker_NBETerm.unembed e3
                                          cb a3 in
                                      FStarC_Compiler_Util.bind_opt uu___8
                                        (fun a31 ->
                                           let uu___9 =
                                             FStarC_TypeChecker_NBETerm.unembed
                                               e4 cb a4 in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___9
                                             (fun a41 ->
                                                let uu___10 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    e5 cb a5 in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___10
                                                  (fun a51 ->
                                                     let uu___11 =
                                                       FStarC_TypeChecker_NBETerm.unembed
                                                         FStarC_Tactics_Embedding.e_proofstate_nbe
                                                         cb a6 in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___11
                                                       (fun ps ->
                                                          let r1 =
                                                            interp_ctx name
                                                              (fun uu___12 ->
                                                                 let uu___13
                                                                   =
                                                                   t a11 a21
                                                                    a31 a41
                                                                    a51 in
                                                                 FStarC_Tactics_Monad.run_safe
                                                                   uu___13 ps) in
                                                          let uu___12 =
                                                            FStarC_TypeChecker_NBETerm.embed
                                                              (FStarC_Tactics_Embedding.e_result_nbe
                                                                 er) cb r1 in
                                                          FStar_Pervasives_Native.Some
                                                            uu___12))))))
                        | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      'r FStarC_TypeChecker_NBETerm.embedding ->
                        FStarC_Syntax_Syntax.universes ->
                          FStarC_TypeChecker_NBETerm.args ->
                            FStarC_TypeChecker_NBETerm.t
                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun er ->
                      fun us ->
                        fun args ->
                          match args with
                          | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                              (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                              (a7, uu___6)::[] ->
                              let uu___7 =
                                FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                              FStarC_Compiler_Util.bind_opt uu___7
                                (fun a11 ->
                                   let uu___8 =
                                     FStarC_TypeChecker_NBETerm.unembed e2 cb
                                       a2 in
                                   FStarC_Compiler_Util.bind_opt uu___8
                                     (fun a21 ->
                                        let uu___9 =
                                          FStarC_TypeChecker_NBETerm.unembed
                                            e3 cb a3 in
                                        FStarC_Compiler_Util.bind_opt uu___9
                                          (fun a31 ->
                                             let uu___10 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 e4 cb a4 in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___10
                                               (fun a41 ->
                                                  let uu___11 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      e5 cb a5 in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___11
                                                    (fun a51 ->
                                                       let uu___12 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           e6 cb a6 in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___12
                                                         (fun a61 ->
                                                            let uu___13 =
                                                              FStarC_TypeChecker_NBETerm.unembed
                                                                FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                cb a7 in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___13
                                                              (fun ps ->
                                                                 let r1 =
                                                                   interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___15
                                                                    ps) in
                                                                 let uu___14
                                                                   =
                                                                   FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu___14)))))))
                          | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        'r FStarC_TypeChecker_NBETerm.embedding ->
                          FStarC_Syntax_Syntax.universes ->
                            FStarC_TypeChecker_NBETerm.args ->
                              FStarC_TypeChecker_NBETerm.t
                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun er ->
                        fun us ->
                          fun args ->
                            match args with
                            | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                (a7, uu___6)::(a8, uu___7)::[] ->
                                let uu___8 =
                                  FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                                FStarC_Compiler_Util.bind_opt uu___8
                                  (fun a11 ->
                                     let uu___9 =
                                       FStarC_TypeChecker_NBETerm.unembed e2
                                         cb a2 in
                                     FStarC_Compiler_Util.bind_opt uu___9
                                       (fun a21 ->
                                          let uu___10 =
                                            FStarC_TypeChecker_NBETerm.unembed
                                              e3 cb a3 in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___10
                                            (fun a31 ->
                                               let uu___11 =
                                                 FStarC_TypeChecker_NBETerm.unembed
                                                   e4 cb a4 in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___11
                                                 (fun a41 ->
                                                    let uu___12 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        e5 cb a5 in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___12
                                                      (fun a51 ->
                                                         let uu___13 =
                                                           FStarC_TypeChecker_NBETerm.unembed
                                                             e6 cb a6 in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___13
                                                           (fun a61 ->
                                                              let uu___14 =
                                                                FStarC_TypeChecker_NBETerm.unembed
                                                                  e7 cb a7 in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___14
                                                                (fun a71 ->
                                                                   let uu___15
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a8 in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___15
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___17
                                                                    ps) in
                                                                    let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___16))))))))
                            | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          'r FStarC_TypeChecker_NBETerm.embedding ->
                            FStarC_Syntax_Syntax.universes ->
                              FStarC_TypeChecker_NBETerm.args ->
                                FStarC_TypeChecker_NBETerm.t
                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun er ->
                          fun us ->
                            fun args ->
                              match args with
                              | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                  (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                  (a7, uu___6)::(a8, uu___7)::(a9, uu___8)::[]
                                  ->
                                  let uu___9 =
                                    FStarC_TypeChecker_NBETerm.unembed e1 cb
                                      a1 in
                                  FStarC_Compiler_Util.bind_opt uu___9
                                    (fun a11 ->
                                       let uu___10 =
                                         FStarC_TypeChecker_NBETerm.unembed
                                           e2 cb a2 in
                                       FStarC_Compiler_Util.bind_opt uu___10
                                         (fun a21 ->
                                            let uu___11 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                e3 cb a3 in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___11
                                              (fun a31 ->
                                                 let uu___12 =
                                                   FStarC_TypeChecker_NBETerm.unembed
                                                     e4 cb a4 in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___12
                                                   (fun a41 ->
                                                      let uu___13 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          e5 cb a5 in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___13
                                                        (fun a51 ->
                                                           let uu___14 =
                                                             FStarC_TypeChecker_NBETerm.unembed
                                                               e6 cb a6 in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___14
                                                             (fun a61 ->
                                                                let uu___15 =
                                                                  FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___15
                                                                  (fun a71 ->
                                                                    let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a81
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___19
                                                                    ps) in
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___18)))))))))
                              | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 -> 't7 -> 't8 -> 't9 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            'r FStarC_TypeChecker_NBETerm.embedding ->
                              FStarC_Syntax_Syntax.universes ->
                                FStarC_TypeChecker_NBETerm.args ->
                                  FStarC_TypeChecker_NBETerm.t
                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun er ->
                            fun us ->
                              fun args ->
                                match args with
                                | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                    (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                    (a7, uu___6)::(a8, uu___7)::(a9, uu___8)::
                                    (a10, uu___9)::[] ->
                                    let uu___10 =
                                      FStarC_TypeChecker_NBETerm.unembed e1
                                        cb a1 in
                                    FStarC_Compiler_Util.bind_opt uu___10
                                      (fun a11 ->
                                         let uu___11 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e2 cb a2 in
                                         FStarC_Compiler_Util.bind_opt
                                           uu___11
                                           (fun a21 ->
                                              let uu___12 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e3 cb a3 in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___12
                                                (fun a31 ->
                                                   let uu___13 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e4 cb a4 in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___13
                                                     (fun a41 ->
                                                        let uu___14 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e5 cb a5 in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___14
                                                          (fun a51 ->
                                                             let uu___15 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e6 cb a6 in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___15
                                                               (fun a61 ->
                                                                  let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (
                                                                    fun a71
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a81
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a91
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___21
                                                                    ps) in
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___20))))))))))
                                | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 -> 't8 -> 't9 -> 't10 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              'r FStarC_TypeChecker_NBETerm.embedding ->
                                FStarC_Syntax_Syntax.universes ->
                                  FStarC_TypeChecker_NBETerm.args ->
                                    FStarC_TypeChecker_NBETerm.t
                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun er ->
                              fun us ->
                                fun args ->
                                  match args with
                                  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                      (a4, uu___3)::(a5, uu___4)::(a6,
                                                                   uu___5)::
                                      (a7, uu___6)::(a8, uu___7)::(a9,
                                                                   uu___8)::
                                      (a10, uu___9)::(a11, uu___10)::[] ->
                                      let uu___11 =
                                        FStarC_TypeChecker_NBETerm.unembed e1
                                          cb a1 in
                                      FStarC_Compiler_Util.bind_opt uu___11
                                        (fun a12 ->
                                           let uu___12 =
                                             FStarC_TypeChecker_NBETerm.unembed
                                               e2 cb a2 in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___12
                                             (fun a21 ->
                                                let uu___13 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    e3 cb a3 in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___13
                                                  (fun a31 ->
                                                     let uu___14 =
                                                       FStarC_TypeChecker_NBETerm.unembed
                                                         e4 cb a4 in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___14
                                                       (fun a41 ->
                                                          let uu___15 =
                                                            FStarC_TypeChecker_NBETerm.unembed
                                                              e5 cb a5 in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___15
                                                            (fun a51 ->
                                                               let uu___16 =
                                                                 FStarC_TypeChecker_NBETerm.unembed
                                                                   e6 cb a6 in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___16
                                                                 (fun a61 ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a71
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a81
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a91
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a101
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    t a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___23
                                                                    ps) in
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___22)))))))))))
                                  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_11 :
  'r 't1 't10 't11 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 -> 't10 -> 't11 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                'r FStarC_TypeChecker_NBETerm.embedding ->
                                  FStarC_Syntax_Syntax.universes ->
                                    FStarC_TypeChecker_NBETerm.args ->
                                      FStarC_TypeChecker_NBETerm.t
                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun er ->
                                fun us ->
                                  fun args ->
                                    match args with
                                    | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                        (a4, uu___3)::(a5, uu___4)::(a6,
                                                                    uu___5)::
                                        (a7, uu___6)::(a8, uu___7)::(a9,
                                                                    uu___8)::
                                        (a10, uu___9)::(a11, uu___10)::
                                        (a12, uu___11)::[] ->
                                        let uu___12 =
                                          FStarC_TypeChecker_NBETerm.unembed
                                            e1 cb a1 in
                                        FStarC_Compiler_Util.bind_opt uu___12
                                          (fun a13 ->
                                             let uu___13 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 e2 cb a2 in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___13
                                               (fun a21 ->
                                                  let uu___14 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      e3 cb a3 in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___14
                                                    (fun a31 ->
                                                       let uu___15 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           e4 cb a4 in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___15
                                                         (fun a41 ->
                                                            let uu___16 =
                                                              FStarC_TypeChecker_NBETerm.unembed
                                                                e5 cb a5 in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___16
                                                              (fun a51 ->
                                                                 let uu___17
                                                                   =
                                                                   FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___17
                                                                   (fun a61
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a71
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a81
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a91
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a101
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a111
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    t a13 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___25
                                                                    ps) in
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___24))))))))))))
                                    | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_12 :
  'r 't1 't10 't11 't12 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 -> 't12 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  'r FStarC_TypeChecker_NBETerm.embedding ->
                                    FStarC_Syntax_Syntax.universes ->
                                      FStarC_TypeChecker_NBETerm.args ->
                                        FStarC_TypeChecker_NBETerm.t
                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun er ->
                                  fun us ->
                                    fun args ->
                                      match args with
                                      | (a1, uu___)::(a2, uu___1)::(a3,
                                                                    uu___2)::
                                          (a4, uu___3)::(a5, uu___4)::
                                          (a6, uu___5)::(a7, uu___6)::
                                          (a8, uu___7)::(a9, uu___8)::
                                          (a10, uu___9)::(a11, uu___10)::
                                          (a12, uu___11)::(a13, uu___12)::[]
                                          ->
                                          let uu___13 =
                                            FStarC_TypeChecker_NBETerm.unembed
                                              e1 cb a1 in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___13
                                            (fun a14 ->
                                               let uu___14 =
                                                 FStarC_TypeChecker_NBETerm.unembed
                                                   e2 cb a2 in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___14
                                                 (fun a21 ->
                                                    let uu___15 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        e3 cb a3 in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___15
                                                      (fun a31 ->
                                                         let uu___16 =
                                                           FStarC_TypeChecker_NBETerm.unembed
                                                             e4 cb a4 in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___16
                                                           (fun a41 ->
                                                              let uu___17 =
                                                                FStarC_TypeChecker_NBETerm.unembed
                                                                  e5 cb a5 in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___17
                                                                (fun a51 ->
                                                                   let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a61
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a71
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a81
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a91
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a101
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a111
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a121
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    t a14 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___27
                                                                    ps) in
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___26)))))))))))))
                                      | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_13 :
  'r 't1 't10 't11 't12 't13 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 -> 't13 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    'r FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      FStarC_Syntax_Syntax.universes ->
                                        FStarC_TypeChecker_NBETerm.args ->
                                          FStarC_TypeChecker_NBETerm.t
                                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun er ->
                                    fun us ->
                                      fun args ->
                                        match args with
                                        | (a1, uu___)::(a2, uu___1)::
                                            (a3, uu___2)::(a4, uu___3)::
                                            (a5, uu___4)::(a6, uu___5)::
                                            (a7, uu___6)::(a8, uu___7)::
                                            (a9, uu___8)::(a10, uu___9)::
                                            (a11, uu___10)::(a12, uu___11)::
                                            (a13, uu___12)::(a14, uu___13)::[]
                                            ->
                                            let uu___14 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                e1 cb a1 in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___14
                                              (fun a15 ->
                                                 let uu___15 =
                                                   FStarC_TypeChecker_NBETerm.unembed
                                                     e2 cb a2 in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___15
                                                   (fun a21 ->
                                                      let uu___16 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          e3 cb a3 in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___16
                                                        (fun a31 ->
                                                           let uu___17 =
                                                             FStarC_TypeChecker_NBETerm.unembed
                                                               e4 cb a4 in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___17
                                                             (fun a41 ->
                                                                let uu___18 =
                                                                  FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___18
                                                                  (fun a51 ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a61
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a71
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a81
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a91
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a101
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a111
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a121
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    t a15 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___29
                                                                    ps) in
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___28))))))))))))))
                                        | uu___ ->
                                            FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_14 :
  'r 't1 't10 't11 't12 't13 't14 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 -> 't14 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      'r FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        FStarC_Syntax_Syntax.universes ->
                                          FStarC_TypeChecker_NBETerm.args ->
                                            FStarC_TypeChecker_NBETerm.t
                                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun er ->
                                      fun us ->
                                        fun args ->
                                          match args with
                                          | (a1, uu___)::(a2, uu___1)::
                                              (a3, uu___2)::(a4, uu___3)::
                                              (a5, uu___4)::(a6, uu___5)::
                                              (a7, uu___6)::(a8, uu___7)::
                                              (a9, uu___8)::(a10, uu___9)::
                                              (a11, uu___10)::(a12, uu___11)::
                                              (a13, uu___12)::(a14, uu___13)::
                                              (a15, uu___14)::[] ->
                                              let uu___15 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e1 cb a1 in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___15
                                                (fun a16 ->
                                                   let uu___16 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e2 cb a2 in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___16
                                                     (fun a21 ->
                                                        let uu___17 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e3 cb a3 in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___17
                                                          (fun a31 ->
                                                             let uu___18 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e4 cb a4 in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___18
                                                               (fun a41 ->
                                                                  let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (
                                                                    fun a51
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a61
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a71
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a81
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a91
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a101
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a111
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a121
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    t a16 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___31
                                                                    ps) in
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___30)))))))))))))))
                                          | uu___ ->
                                              FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_15 :
  'r 't1 't10 't11 't12 't13 't14 't15 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        'r
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          FStarC_Syntax_Syntax.universes ->
                                            FStarC_TypeChecker_NBETerm.args
                                              ->
                                              FStarC_TypeChecker_NBETerm.t
                                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun er ->
                                        fun us ->
                                          fun args ->
                                            match args with
                                            | (a1, uu___)::(a2, uu___1)::
                                                (a3, uu___2)::(a4, uu___3)::
                                                (a5, uu___4)::(a6, uu___5)::
                                                (a7, uu___6)::(a8, uu___7)::
                                                (a9, uu___8)::(a10, uu___9)::
                                                (a11, uu___10)::(a12,
                                                                 uu___11)::
                                                (a13, uu___12)::(a14,
                                                                 uu___13)::
                                                (a15, uu___14)::(a16,
                                                                 uu___15)::[]
                                                ->
                                                let uu___16 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    e1 cb a1 in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___16
                                                  (fun a17 ->
                                                     let uu___17 =
                                                       FStarC_TypeChecker_NBETerm.unembed
                                                         e2 cb a2 in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___17
                                                       (fun a21 ->
                                                          let uu___18 =
                                                            FStarC_TypeChecker_NBETerm.unembed
                                                              e3 cb a3 in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___18
                                                            (fun a31 ->
                                                               let uu___19 =
                                                                 FStarC_TypeChecker_NBETerm.unembed
                                                                   e4 cb a4 in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___19
                                                                 (fun a41 ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a51
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a61
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a71
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a81
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a91
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a101
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a111
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a121
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    t a17 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___33
                                                                    ps) in
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___32))))))))))))))))
                                            | uu___ ->
                                                FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_16 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 ->
                                       't16 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          'r
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            FStarC_Syntax_Syntax.universes ->
                                              FStarC_TypeChecker_NBETerm.args
                                                ->
                                                FStarC_TypeChecker_NBETerm.t
                                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun er ->
                                          fun us ->
                                            fun args ->
                                              match args with
                                              | (a1, uu___)::(a2, uu___1)::
                                                  (a3, uu___2)::(a4, uu___3)::
                                                  (a5, uu___4)::(a6, uu___5)::
                                                  (a7, uu___6)::(a8, uu___7)::
                                                  (a9, uu___8)::(a10, uu___9)::
                                                  (a11, uu___10)::(a12,
                                                                   uu___11)::
                                                  (a13, uu___12)::(a14,
                                                                   uu___13)::
                                                  (a15, uu___14)::(a16,
                                                                   uu___15)::
                                                  (a17, uu___16)::[] ->
                                                  let uu___17 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      e1 cb a1 in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___17
                                                    (fun a18 ->
                                                       let uu___18 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           e2 cb a2 in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___18
                                                         (fun a21 ->
                                                            let uu___19 =
                                                              FStarC_TypeChecker_NBETerm.unembed
                                                                e3 cb a3 in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___19
                                                              (fun a31 ->
                                                                 let uu___20
                                                                   =
                                                                   FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___20
                                                                   (fun a41
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a51
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a61
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a71
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a81
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a91
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a101
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a111
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a121
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    t a18 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___35
                                                                    ps) in
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___34)))))))))))))))))
                                              | uu___ ->
                                                  FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_17 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't2 't3 't4 't5 't6 't7 't8
    't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 ->
                                       't16 ->
                                         't17 -> 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            'r
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              FStarC_Syntax_Syntax.universes
                                                ->
                                                FStarC_TypeChecker_NBETerm.args
                                                  ->
                                                  FStarC_TypeChecker_NBETerm.t
                                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun er ->
                                            fun us ->
                                              fun args ->
                                                match args with
                                                | (a1, uu___)::(a2, uu___1)::
                                                    (a3, uu___2)::(a4,
                                                                   uu___3)::
                                                    (a5, uu___4)::(a6,
                                                                   uu___5)::
                                                    (a7, uu___6)::(a8,
                                                                   uu___7)::
                                                    (a9, uu___8)::(a10,
                                                                   uu___9)::
                                                    (a11, uu___10)::(a12,
                                                                    uu___11)::
                                                    (a13, uu___12)::(a14,
                                                                    uu___13)::
                                                    (a15, uu___14)::(a16,
                                                                    uu___15)::
                                                    (a17, uu___16)::(a18,
                                                                    uu___17)::[]
                                                    ->
                                                    let uu___18 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        e1 cb a1 in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___18
                                                      (fun a19 ->
                                                         let uu___19 =
                                                           FStarC_TypeChecker_NBETerm.unembed
                                                             e2 cb a2 in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___19
                                                           (fun a21 ->
                                                              let uu___20 =
                                                                FStarC_TypeChecker_NBETerm.unembed
                                                                  e3 cb a3 in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___20
                                                                (fun a31 ->
                                                                   let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a41
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a51
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a61
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a71
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a81
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a91
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a101
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a111
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a121
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a18 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    t a19 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161
                                                                    a171 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___37
                                                                    ps) in
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___36))))))))))))))))))
                                                | uu___ ->
                                                    FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_18 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't2 't3 't4 't5 't6 't7
    't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 ->
                                       't16 ->
                                         't17 ->
                                           't18 ->
                                             'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            't18
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              'r
                                                FStarC_TypeChecker_NBETerm.embedding
                                                ->
                                                FStarC_Syntax_Syntax.universes
                                                  ->
                                                  FStarC_TypeChecker_NBETerm.args
                                                    ->
                                                    FStarC_TypeChecker_NBETerm.t
                                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun e18 ->
                                            fun er ->
                                              fun us ->
                                                fun args ->
                                                  match args with
                                                  | (a1, uu___)::(a2, uu___1)::
                                                      (a3, uu___2)::(a4,
                                                                    uu___3)::
                                                      (a5, uu___4)::(a6,
                                                                    uu___5)::
                                                      (a7, uu___6)::(a8,
                                                                    uu___7)::
                                                      (a9, uu___8)::(a10,
                                                                    uu___9)::
                                                      (a11, uu___10)::
                                                      (a12, uu___11)::
                                                      (a13, uu___12)::
                                                      (a14, uu___13)::
                                                      (a15, uu___14)::
                                                      (a16, uu___15)::
                                                      (a17, uu___16)::
                                                      (a18, uu___17)::
                                                      (a19, uu___18)::[] ->
                                                      let uu___19 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          e1 cb a1 in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___19
                                                        (fun a110 ->
                                                           let uu___20 =
                                                             FStarC_TypeChecker_NBETerm.unembed
                                                               e2 cb a2 in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___20
                                                             (fun a21 ->
                                                                let uu___21 =
                                                                  FStarC_TypeChecker_NBETerm.unembed
                                                                    e3 cb a3 in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___21
                                                                  (fun a31 ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a41
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a51
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a61
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a71
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a81
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a91
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a101
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a111
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a121
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a19 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    t a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___39
                                                                    ps) in
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___38)))))))))))))))))))
                                                  | uu___ ->
                                                      FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_19 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't3 't4 't5
    't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 ->
                                       't16 ->
                                         't17 ->
                                           't18 ->
                                             't19 ->
                                               'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            't18
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              't19
                                                FStarC_TypeChecker_NBETerm.embedding
                                                ->
                                                'r
                                                  FStarC_TypeChecker_NBETerm.embedding
                                                  ->
                                                  FStarC_Syntax_Syntax.universes
                                                    ->
                                                    FStarC_TypeChecker_NBETerm.args
                                                      ->
                                                      FStarC_TypeChecker_NBETerm.t
                                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun e18 ->
                                            fun e19 ->
                                              fun er ->
                                                fun us ->
                                                  fun args ->
                                                    match args with
                                                    | (a1, uu___)::(a2,
                                                                    uu___1)::
                                                        (a3, uu___2)::
                                                        (a4, uu___3)::
                                                        (a5, uu___4)::
                                                        (a6, uu___5)::
                                                        (a7, uu___6)::
                                                        (a8, uu___7)::
                                                        (a9, uu___8)::
                                                        (a10, uu___9)::
                                                        (a11, uu___10)::
                                                        (a12, uu___11)::
                                                        (a13, uu___12)::
                                                        (a14, uu___13)::
                                                        (a15, uu___14)::
                                                        (a16, uu___15)::
                                                        (a17, uu___16)::
                                                        (a18, uu___17)::
                                                        (a19, uu___18)::
                                                        (a20, uu___19)::[] ->
                                                        let uu___20 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e1 cb a1 in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___20
                                                          (fun a110 ->
                                                             let uu___21 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e2 cb a2 in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___21
                                                               (fun a21 ->
                                                                  let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e3 cb a3 in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (
                                                                    fun a31
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a41
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a51
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a61
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a71
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a81
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a91
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a101
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a111
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a121
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a20 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___39
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    t a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___41
                                                                    ps) in
                                                                    let uu___40
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___40))))))))))))))))))))
                                                    | uu___ ->
                                                        FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_20 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't20 't3 't4
    't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 ->
                                       't16 ->
                                         't17 ->
                                           't18 ->
                                             't19 ->
                                               't20 ->
                                                 'r FStarC_Tactics_Monad.tac)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            't18
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              't19
                                                FStarC_TypeChecker_NBETerm.embedding
                                                ->
                                                't20
                                                  FStarC_TypeChecker_NBETerm.embedding
                                                  ->
                                                  'r
                                                    FStarC_TypeChecker_NBETerm.embedding
                                                    ->
                                                    FStarC_Syntax_Syntax.universes
                                                      ->
                                                      FStarC_TypeChecker_NBETerm.args
                                                        ->
                                                        FStarC_TypeChecker_NBETerm.t
                                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun t ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun e18 ->
                                            fun e19 ->
                                              fun e20 ->
                                                fun er ->
                                                  fun us ->
                                                    fun args ->
                                                      match args with
                                                      | (a1, uu___)::
                                                          (a2, uu___1)::
                                                          (a3, uu___2)::
                                                          (a4, uu___3)::
                                                          (a5, uu___4)::
                                                          (a6, uu___5)::
                                                          (a7, uu___6)::
                                                          (a8, uu___7)::
                                                          (a9, uu___8)::
                                                          (a10, uu___9)::
                                                          (a11, uu___10)::
                                                          (a12, uu___11)::
                                                          (a13, uu___12)::
                                                          (a14, uu___13)::
                                                          (a15, uu___14)::
                                                          (a16, uu___15)::
                                                          (a17, uu___16)::
                                                          (a18, uu___17)::
                                                          (a19, uu___18)::
                                                          (a20, uu___19)::
                                                          (a21, uu___20)::[]
                                                          ->
                                                          let uu___21 =
                                                            FStarC_TypeChecker_NBETerm.unembed
                                                              e1 cb a1 in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___21
                                                            (fun a110 ->
                                                               let uu___22 =
                                                                 FStarC_TypeChecker_NBETerm.unembed
                                                                   e2 cb a2 in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___22
                                                                 (fun a22 ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e3 cb a3 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a31
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a41
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a51
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a61
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a71
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a81
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a91
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a101
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a111
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a121
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a131
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a141
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a151
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a161
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a171
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___38
                                                                    (fun a181
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___39
                                                                    (fun a191
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e20 cb
                                                                    a20 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___40
                                                                    (fun a201
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_proofstate_nbe
                                                                    cb a21 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___41
                                                                    (fun ps
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    t a110
                                                                    a22 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191
                                                                    a201 in
                                                                    FStarC_Tactics_Monad.run_safe
                                                                    uu___43
                                                                    ps) in
                                                                    let uu___42
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (FStarC_Tactics_Embedding.e_result_nbe
                                                                    er) cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___42)))))))))))))))))))))
                                                      | uu___ ->
                                                          FStar_Pervasives_Native.None
let mk_total_interpretation_1 :
  'r 't1 .
    Prims.string ->
      ('t1 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          'r FStarC_Syntax_Embeddings_Base.embedding ->
            FStarC_TypeChecker_Primops_Base.psc ->
              FStarC_Syntax_Embeddings_Base.norm_cb ->
                FStarC_Syntax_Syntax.universes ->
                  FStarC_Syntax_Syntax.args ->
                    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun er ->
          fun psc ->
            fun ncb ->
              fun us ->
                fun args ->
                  match args with
                  | (a1, uu___)::[] ->
                      let uu___1 = unembed e1 a1 ncb in
                      FStarC_Compiler_Util.bind_opt uu___1
                        (fun a11 ->
                           let r1 = interp_ctx name (fun uu___2 -> f a11) in
                           let uu___2 =
                             let uu___3 =
                               FStarC_TypeChecker_Primops_Base.psc_range psc in
                             embed er uu___3 r1 ncb in
                           FStar_Pervasives_Native.Some uu___2)
                  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_2 :
  'r 't1 't2 .
    Prims.string ->
      ('t1 -> 't2 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            'r FStarC_Syntax_Embeddings_Base.embedding ->
              FStarC_TypeChecker_Primops_Base.psc ->
                FStarC_Syntax_Embeddings_Base.norm_cb ->
                  FStarC_Syntax_Syntax.universes ->
                    FStarC_Syntax_Syntax.args ->
                      FStarC_Syntax_Syntax.term
                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun er ->
            fun psc ->
              fun ncb ->
                fun us ->
                  fun args ->
                    match args with
                    | (a1, uu___)::(a2, uu___1)::[] ->
                        let uu___2 = unembed e1 a1 ncb in
                        FStarC_Compiler_Util.bind_opt uu___2
                          (fun a11 ->
                             let uu___3 = unembed e2 a2 ncb in
                             FStarC_Compiler_Util.bind_opt uu___3
                               (fun a21 ->
                                  let r1 =
                                    interp_ctx name (fun uu___4 -> f a11 a21) in
                                  let uu___4 =
                                    let uu___5 =
                                      FStarC_TypeChecker_Primops_Base.psc_range
                                        psc in
                                    embed er uu___5 r1 ncb in
                                  FStar_Pervasives_Native.Some uu___4))
                    | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_3 :
  'r 't1 't2 't3 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              'r FStarC_Syntax_Embeddings_Base.embedding ->
                FStarC_TypeChecker_Primops_Base.psc ->
                  FStarC_Syntax_Embeddings_Base.norm_cb ->
                    FStarC_Syntax_Syntax.universes ->
                      FStarC_Syntax_Syntax.args ->
                        FStarC_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun er ->
              fun psc ->
                fun ncb ->
                  fun us ->
                    fun args ->
                      match args with
                      | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
                          let uu___3 = unembed e1 a1 ncb in
                          FStarC_Compiler_Util.bind_opt uu___3
                            (fun a11 ->
                               let uu___4 = unembed e2 a2 ncb in
                               FStarC_Compiler_Util.bind_opt uu___4
                                 (fun a21 ->
                                    let uu___5 = unembed e3 a3 ncb in
                                    FStarC_Compiler_Util.bind_opt uu___5
                                      (fun a31 ->
                                         let r1 =
                                           interp_ctx name
                                             (fun uu___6 -> f a11 a21 a31) in
                                         let uu___6 =
                                           let uu___7 =
                                             FStarC_TypeChecker_Primops_Base.psc_range
                                               psc in
                                           embed er uu___7 r1 ncb in
                                         FStar_Pervasives_Native.Some uu___6)))
                      | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_4 :
  'r 't1 't2 't3 't4 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                'r FStarC_Syntax_Embeddings_Base.embedding ->
                  FStarC_TypeChecker_Primops_Base.psc ->
                    FStarC_Syntax_Embeddings_Base.norm_cb ->
                      FStarC_Syntax_Syntax.universes ->
                        FStarC_Syntax_Syntax.args ->
                          FStarC_Syntax_Syntax.term
                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun er ->
                fun psc ->
                  fun ncb ->
                    fun us ->
                      fun args ->
                        match args with
                        | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4,
                                                                    uu___3)::[]
                            ->
                            let uu___4 = unembed e1 a1 ncb in
                            FStarC_Compiler_Util.bind_opt uu___4
                              (fun a11 ->
                                 let uu___5 = unembed e2 a2 ncb in
                                 FStarC_Compiler_Util.bind_opt uu___5
                                   (fun a21 ->
                                      let uu___6 = unembed e3 a3 ncb in
                                      FStarC_Compiler_Util.bind_opt uu___6
                                        (fun a31 ->
                                           let uu___7 = unembed e4 a4 ncb in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___7
                                             (fun a41 ->
                                                let r1 =
                                                  interp_ctx name
                                                    (fun uu___8 ->
                                                       f a11 a21 a31 a41) in
                                                let uu___8 =
                                                  let uu___9 =
                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                      psc in
                                                  embed er uu___9 r1 ncb in
                                                FStar_Pervasives_Native.Some
                                                  uu___8))))
                        | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  'r FStarC_Syntax_Embeddings_Base.embedding ->
                    FStarC_TypeChecker_Primops_Base.psc ->
                      FStarC_Syntax_Embeddings_Base.norm_cb ->
                        FStarC_Syntax_Syntax.universes ->
                          FStarC_Syntax_Syntax.args ->
                            FStarC_Syntax_Syntax.term
                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun er ->
                  fun psc ->
                    fun ncb ->
                      fun us ->
                        fun args ->
                          match args with
                          | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                              (a4, uu___3)::(a5, uu___4)::[] ->
                              let uu___5 = unembed e1 a1 ncb in
                              FStarC_Compiler_Util.bind_opt uu___5
                                (fun a11 ->
                                   let uu___6 = unembed e2 a2 ncb in
                                   FStarC_Compiler_Util.bind_opt uu___6
                                     (fun a21 ->
                                        let uu___7 = unembed e3 a3 ncb in
                                        FStarC_Compiler_Util.bind_opt uu___7
                                          (fun a31 ->
                                             let uu___8 = unembed e4 a4 ncb in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___8
                                               (fun a41 ->
                                                  let uu___9 =
                                                    unembed e5 a5 ncb in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___9
                                                    (fun a51 ->
                                                       let r1 =
                                                         interp_ctx name
                                                           (fun uu___10 ->
                                                              f a11 a21 a31
                                                                a41 a51) in
                                                       let uu___10 =
                                                         let uu___11 =
                                                           FStarC_TypeChecker_Primops_Base.psc_range
                                                             psc in
                                                         embed er uu___11 r1
                                                           ncb in
                                                       FStar_Pervasives_Native.Some
                                                         uu___10)))))
                          | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    'r FStarC_Syntax_Embeddings_Base.embedding ->
                      FStarC_TypeChecker_Primops_Base.psc ->
                        FStarC_Syntax_Embeddings_Base.norm_cb ->
                          FStarC_Syntax_Syntax.universes ->
                            FStarC_Syntax_Syntax.args ->
                              FStarC_Syntax_Syntax.term
                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun er ->
                    fun psc ->
                      fun ncb ->
                        fun us ->
                          fun args ->
                            match args with
                            | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::[]
                                ->
                                let uu___6 = unembed e1 a1 ncb in
                                FStarC_Compiler_Util.bind_opt uu___6
                                  (fun a11 ->
                                     let uu___7 = unembed e2 a2 ncb in
                                     FStarC_Compiler_Util.bind_opt uu___7
                                       (fun a21 ->
                                          let uu___8 = unembed e3 a3 ncb in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___8
                                            (fun a31 ->
                                               let uu___9 = unembed e4 a4 ncb in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___9
                                                 (fun a41 ->
                                                    let uu___10 =
                                                      unembed e5 a5 ncb in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___10
                                                      (fun a51 ->
                                                         let uu___11 =
                                                           unembed e6 a6 ncb in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___11
                                                           (fun a61 ->
                                                              let r1 =
                                                                interp_ctx
                                                                  name
                                                                  (fun
                                                                    uu___12
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61) in
                                                              let uu___12 =
                                                                let uu___13 =
                                                                  FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                embed er
                                                                  uu___13 r1
                                                                  ncb in
                                                              FStar_Pervasives_Native.Some
                                                                uu___12))))))
                            | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      'r FStarC_Syntax_Embeddings_Base.embedding ->
                        FStarC_TypeChecker_Primops_Base.psc ->
                          FStarC_Syntax_Embeddings_Base.norm_cb ->
                            FStarC_Syntax_Syntax.universes ->
                              FStarC_Syntax_Syntax.args ->
                                FStarC_Syntax_Syntax.term
                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun er ->
                      fun psc ->
                        fun ncb ->
                          fun us ->
                            fun args ->
                              match args with
                              | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                  (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                  (a7, uu___6)::[] ->
                                  let uu___7 = unembed e1 a1 ncb in
                                  FStarC_Compiler_Util.bind_opt uu___7
                                    (fun a11 ->
                                       let uu___8 = unembed e2 a2 ncb in
                                       FStarC_Compiler_Util.bind_opt uu___8
                                         (fun a21 ->
                                            let uu___9 = unembed e3 a3 ncb in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___9
                                              (fun a31 ->
                                                 let uu___10 =
                                                   unembed e4 a4 ncb in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___10
                                                   (fun a41 ->
                                                      let uu___11 =
                                                        unembed e5 a5 ncb in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___11
                                                        (fun a51 ->
                                                           let uu___12 =
                                                             unembed e6 a6
                                                               ncb in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___12
                                                             (fun a61 ->
                                                                let uu___13 =
                                                                  unembed e7
                                                                    a7 ncb in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___13
                                                                  (fun a71 ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71) in
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___15
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___14)))))))
                              | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        'r FStarC_Syntax_Embeddings_Base.embedding ->
                          FStarC_TypeChecker_Primops_Base.psc ->
                            FStarC_Syntax_Embeddings_Base.norm_cb ->
                              FStarC_Syntax_Syntax.universes ->
                                FStarC_Syntax_Syntax.args ->
                                  FStarC_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun er ->
                        fun psc ->
                          fun ncb ->
                            fun us ->
                              fun args ->
                                match args with
                                | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                    (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                    (a7, uu___6)::(a8, uu___7)::[] ->
                                    let uu___8 = unembed e1 a1 ncb in
                                    FStarC_Compiler_Util.bind_opt uu___8
                                      (fun a11 ->
                                         let uu___9 = unembed e2 a2 ncb in
                                         FStarC_Compiler_Util.bind_opt uu___9
                                           (fun a21 ->
                                              let uu___10 = unembed e3 a3 ncb in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___10
                                                (fun a31 ->
                                                   let uu___11 =
                                                     unembed e4 a4 ncb in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___11
                                                     (fun a41 ->
                                                        let uu___12 =
                                                          unembed e5 a5 ncb in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___12
                                                          (fun a51 ->
                                                             let uu___13 =
                                                               unembed e6 a6
                                                                 ncb in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___13
                                                               (fun a61 ->
                                                                  let uu___14
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___14
                                                                    (
                                                                    fun a71
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___15
                                                                    (fun a81
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81) in
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___17
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___16))))))))
                                | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r) ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          'r FStarC_Syntax_Embeddings_Base.embedding ->
                            FStarC_TypeChecker_Primops_Base.psc ->
                              FStarC_Syntax_Embeddings_Base.norm_cb ->
                                FStarC_Syntax_Syntax.universes ->
                                  FStarC_Syntax_Syntax.args ->
                                    FStarC_Syntax_Syntax.term
                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun er ->
                          fun psc ->
                            fun ncb ->
                              fun us ->
                                fun args ->
                                  match args with
                                  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                      (a4, uu___3)::(a5, uu___4)::(a6,
                                                                   uu___5)::
                                      (a7, uu___6)::(a8, uu___7)::(a9,
                                                                   uu___8)::[]
                                      ->
                                      let uu___9 = unembed e1 a1 ncb in
                                      FStarC_Compiler_Util.bind_opt uu___9
                                        (fun a11 ->
                                           let uu___10 = unembed e2 a2 ncb in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___10
                                             (fun a21 ->
                                                let uu___11 =
                                                  unembed e3 a3 ncb in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___11
                                                  (fun a31 ->
                                                     let uu___12 =
                                                       unembed e4 a4 ncb in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___12
                                                       (fun a41 ->
                                                          let uu___13 =
                                                            unembed e5 a5 ncb in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___13
                                                            (fun a51 ->
                                                               let uu___14 =
                                                                 unembed e6
                                                                   a6 ncb in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___14
                                                                 (fun a61 ->
                                                                    let uu___15
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___15
                                                                    (fun a71
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a81
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a91
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91) in
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___19
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___18)))))))))
                                  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            'r FStarC_Syntax_Embeddings_Base.embedding ->
                              FStarC_TypeChecker_Primops_Base.psc ->
                                FStarC_Syntax_Embeddings_Base.norm_cb ->
                                  FStarC_Syntax_Syntax.universes ->
                                    FStarC_Syntax_Syntax.args ->
                                      FStarC_Syntax_Syntax.term
                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun er ->
                            fun psc ->
                              fun ncb ->
                                fun us ->
                                  fun args ->
                                    match args with
                                    | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                        (a4, uu___3)::(a5, uu___4)::(a6,
                                                                    uu___5)::
                                        (a7, uu___6)::(a8, uu___7)::(a9,
                                                                    uu___8)::
                                        (a10, uu___9)::[] ->
                                        let uu___10 = unembed e1 a1 ncb in
                                        FStarC_Compiler_Util.bind_opt uu___10
                                          (fun a11 ->
                                             let uu___11 = unembed e2 a2 ncb in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___11
                                               (fun a21 ->
                                                  let uu___12 =
                                                    unembed e3 a3 ncb in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___12
                                                    (fun a31 ->
                                                       let uu___13 =
                                                         unembed e4 a4 ncb in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___13
                                                         (fun a41 ->
                                                            let uu___14 =
                                                              unembed e5 a5
                                                                ncb in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___14
                                                              (fun a51 ->
                                                                 let uu___15
                                                                   =
                                                                   unembed e6
                                                                    a6 ncb in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___15
                                                                   (fun a61
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a71
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a81
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a91
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a101
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101) in
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___21
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___20))))))))))
                                    | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_11 :
  'r 't1 't10 't11 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              'r FStarC_Syntax_Embeddings_Base.embedding ->
                                FStarC_TypeChecker_Primops_Base.psc ->
                                  FStarC_Syntax_Embeddings_Base.norm_cb ->
                                    FStarC_Syntax_Syntax.universes ->
                                      FStarC_Syntax_Syntax.args ->
                                        FStarC_Syntax_Syntax.term
                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun er ->
                              fun psc ->
                                fun ncb ->
                                  fun us ->
                                    fun args ->
                                      match args with
                                      | (a1, uu___)::(a2, uu___1)::(a3,
                                                                    uu___2)::
                                          (a4, uu___3)::(a5, uu___4)::
                                          (a6, uu___5)::(a7, uu___6)::
                                          (a8, uu___7)::(a9, uu___8)::
                                          (a10, uu___9)::(a11, uu___10)::[]
                                          ->
                                          let uu___11 = unembed e1 a1 ncb in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___11
                                            (fun a12 ->
                                               let uu___12 =
                                                 unembed e2 a2 ncb in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___12
                                                 (fun a21 ->
                                                    let uu___13 =
                                                      unembed e3 a3 ncb in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___13
                                                      (fun a31 ->
                                                         let uu___14 =
                                                           unembed e4 a4 ncb in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___14
                                                           (fun a41 ->
                                                              let uu___15 =
                                                                unembed e5 a5
                                                                  ncb in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___15
                                                                (fun a51 ->
                                                                   let uu___16
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a61
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a71
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a81
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a91
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a101
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a111
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    f a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111) in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___23
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___22)))))))))))
                                      | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_12 :
  'r 't1 't10 't11 't12 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                'r FStarC_Syntax_Embeddings_Base.embedding ->
                                  FStarC_TypeChecker_Primops_Base.psc ->
                                    FStarC_Syntax_Embeddings_Base.norm_cb ->
                                      FStarC_Syntax_Syntax.universes ->
                                        FStarC_Syntax_Syntax.args ->
                                          FStarC_Syntax_Syntax.term
                                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun er ->
                                fun psc ->
                                  fun ncb ->
                                    fun us ->
                                      fun args ->
                                        match args with
                                        | (a1, uu___)::(a2, uu___1)::
                                            (a3, uu___2)::(a4, uu___3)::
                                            (a5, uu___4)::(a6, uu___5)::
                                            (a7, uu___6)::(a8, uu___7)::
                                            (a9, uu___8)::(a10, uu___9)::
                                            (a11, uu___10)::(a12, uu___11)::[]
                                            ->
                                            let uu___12 = unembed e1 a1 ncb in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___12
                                              (fun a13 ->
                                                 let uu___13 =
                                                   unembed e2 a2 ncb in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___13
                                                   (fun a21 ->
                                                      let uu___14 =
                                                        unembed e3 a3 ncb in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___14
                                                        (fun a31 ->
                                                           let uu___15 =
                                                             unembed e4 a4
                                                               ncb in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___15
                                                             (fun a41 ->
                                                                let uu___16 =
                                                                  unembed e5
                                                                    a5 ncb in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___16
                                                                  (fun a51 ->
                                                                    let uu___17
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a61
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a71
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a81
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a91
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a101
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a111
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a121
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    f a13 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121) in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___25
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___24))))))))))))
                                        | uu___ ->
                                            FStar_Pervasives_Native.None
let mk_total_interpretation_13 :
  'r 't1 't10 't11 't12 't13 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  'r FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    FStarC_TypeChecker_Primops_Base.psc ->
                                      FStarC_Syntax_Embeddings_Base.norm_cb
                                        ->
                                        FStarC_Syntax_Syntax.universes ->
                                          FStarC_Syntax_Syntax.args ->
                                            FStarC_Syntax_Syntax.term
                                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun er ->
                                  fun psc ->
                                    fun ncb ->
                                      fun us ->
                                        fun args ->
                                          match args with
                                          | (a1, uu___)::(a2, uu___1)::
                                              (a3, uu___2)::(a4, uu___3)::
                                              (a5, uu___4)::(a6, uu___5)::
                                              (a7, uu___6)::(a8, uu___7)::
                                              (a9, uu___8)::(a10, uu___9)::
                                              (a11, uu___10)::(a12, uu___11)::
                                              (a13, uu___12)::[] ->
                                              let uu___13 = unembed e1 a1 ncb in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___13
                                                (fun a14 ->
                                                   let uu___14 =
                                                     unembed e2 a2 ncb in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___14
                                                     (fun a21 ->
                                                        let uu___15 =
                                                          unembed e3 a3 ncb in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___15
                                                          (fun a31 ->
                                                             let uu___16 =
                                                               unembed e4 a4
                                                                 ncb in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___16
                                                               (fun a41 ->
                                                                  let uu___17
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (
                                                                    fun a51
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a61
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a71
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a81
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a91
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a101
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a111
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a121
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a131
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    f a14 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131) in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___27
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___26)))))))))))))
                                          | uu___ ->
                                              FStar_Pervasives_Native.None
let mk_total_interpretation_14 :
  'r 't1 't10 't11 't12 't13 't14 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    'r
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      FStarC_TypeChecker_Primops_Base.psc ->
                                        FStarC_Syntax_Embeddings_Base.norm_cb
                                          ->
                                          FStarC_Syntax_Syntax.universes ->
                                            FStarC_Syntax_Syntax.args ->
                                              FStarC_Syntax_Syntax.term
                                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun er ->
                                    fun psc ->
                                      fun ncb ->
                                        fun us ->
                                          fun args ->
                                            match args with
                                            | (a1, uu___)::(a2, uu___1)::
                                                (a3, uu___2)::(a4, uu___3)::
                                                (a5, uu___4)::(a6, uu___5)::
                                                (a7, uu___6)::(a8, uu___7)::
                                                (a9, uu___8)::(a10, uu___9)::
                                                (a11, uu___10)::(a12,
                                                                 uu___11)::
                                                (a13, uu___12)::(a14,
                                                                 uu___13)::[]
                                                ->
                                                let uu___14 =
                                                  unembed e1 a1 ncb in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___14
                                                  (fun a15 ->
                                                     let uu___15 =
                                                       unembed e2 a2 ncb in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___15
                                                       (fun a21 ->
                                                          let uu___16 =
                                                            unembed e3 a3 ncb in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___16
                                                            (fun a31 ->
                                                               let uu___17 =
                                                                 unembed e4
                                                                   a4 ncb in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___17
                                                                 (fun a41 ->
                                                                    let uu___18
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a51
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a61
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a71
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a81
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a91
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a101
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a111
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a121
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a141
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    f a15 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141) in
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___29
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___28))))))))))))))
                                            | uu___ ->
                                                FStar_Pervasives_Native.None
let mk_total_interpretation_15 :
  'r 't1 't10 't11 't12 't13 't14 't15 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 't15 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      'r
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        FStarC_TypeChecker_Primops_Base.psc
                                          ->
                                          FStarC_Syntax_Embeddings_Base.norm_cb
                                            ->
                                            FStarC_Syntax_Syntax.universes ->
                                              FStarC_Syntax_Syntax.args ->
                                                FStarC_Syntax_Syntax.term
                                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun er ->
                                      fun psc ->
                                        fun ncb ->
                                          fun us ->
                                            fun args ->
                                              match args with
                                              | (a1, uu___)::(a2, uu___1)::
                                                  (a3, uu___2)::(a4, uu___3)::
                                                  (a5, uu___4)::(a6, uu___5)::
                                                  (a7, uu___6)::(a8, uu___7)::
                                                  (a9, uu___8)::(a10, uu___9)::
                                                  (a11, uu___10)::(a12,
                                                                   uu___11)::
                                                  (a13, uu___12)::(a14,
                                                                   uu___13)::
                                                  (a15, uu___14)::[] ->
                                                  let uu___15 =
                                                    unembed e1 a1 ncb in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___15
                                                    (fun a16 ->
                                                       let uu___16 =
                                                         unembed e2 a2 ncb in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___16
                                                         (fun a21 ->
                                                            let uu___17 =
                                                              unembed e3 a3
                                                                ncb in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___17
                                                              (fun a31 ->
                                                                 let uu___18
                                                                   =
                                                                   unembed e4
                                                                    a4 ncb in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___18
                                                                   (fun a41
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a51
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a61
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a71
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a81
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a91
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a101
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a111
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a121
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a151
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    f a16 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151) in
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___31
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___30)))))))))))))))
                                              | uu___ ->
                                                  FStar_Pervasives_Native.None
let mk_total_interpretation_16 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 -> 't12 -> 't13 -> 't14 -> 't15 -> 't16 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        'r
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          FStarC_TypeChecker_Primops_Base.psc
                                            ->
                                            FStarC_Syntax_Embeddings_Base.norm_cb
                                              ->
                                              FStarC_Syntax_Syntax.universes
                                                ->
                                                FStarC_Syntax_Syntax.args ->
                                                  FStarC_Syntax_Syntax.term
                                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun er ->
                                        fun psc ->
                                          fun ncb ->
                                            fun us ->
                                              fun args ->
                                                match args with
                                                | (a1, uu___)::(a2, uu___1)::
                                                    (a3, uu___2)::(a4,
                                                                   uu___3)::
                                                    (a5, uu___4)::(a6,
                                                                   uu___5)::
                                                    (a7, uu___6)::(a8,
                                                                   uu___7)::
                                                    (a9, uu___8)::(a10,
                                                                   uu___9)::
                                                    (a11, uu___10)::(a12,
                                                                    uu___11)::
                                                    (a13, uu___12)::(a14,
                                                                    uu___13)::
                                                    (a15, uu___14)::(a16,
                                                                    uu___15)::[]
                                                    ->
                                                    let uu___16 =
                                                      unembed e1 a1 ncb in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___16
                                                      (fun a17 ->
                                                         let uu___17 =
                                                           unembed e2 a2 ncb in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___17
                                                           (fun a21 ->
                                                              let uu___18 =
                                                                unembed e3 a3
                                                                  ncb in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___18
                                                                (fun a31 ->
                                                                   let uu___19
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a41
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a51
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a61
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a71
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a81
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a91
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a101
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a111
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a121
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a161
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    f a17 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161) in
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___33
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___32))))))))))))))))
                                                | uu___ ->
                                                    FStar_Pervasives_Native.None
let mk_total_interpretation_17 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't2 't3 't4 't5 't6 't7 't8
    't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 -> 't14 -> 't15 -> 't16 -> 't17 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          'r
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            FStarC_TypeChecker_Primops_Base.psc
                                              ->
                                              FStarC_Syntax_Embeddings_Base.norm_cb
                                                ->
                                                FStarC_Syntax_Syntax.universes
                                                  ->
                                                  FStarC_Syntax_Syntax.args
                                                    ->
                                                    FStarC_Syntax_Syntax.term
                                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun er ->
                                          fun psc ->
                                            fun ncb ->
                                              fun us ->
                                                fun args ->
                                                  match args with
                                                  | (a1, uu___)::(a2, uu___1)::
                                                      (a3, uu___2)::(a4,
                                                                    uu___3)::
                                                      (a5, uu___4)::(a6,
                                                                    uu___5)::
                                                      (a7, uu___6)::(a8,
                                                                    uu___7)::
                                                      (a9, uu___8)::(a10,
                                                                    uu___9)::
                                                      (a11, uu___10)::
                                                      (a12, uu___11)::
                                                      (a13, uu___12)::
                                                      (a14, uu___13)::
                                                      (a15, uu___14)::
                                                      (a16, uu___15)::
                                                      (a17, uu___16)::[] ->
                                                      let uu___17 =
                                                        unembed e1 a1 ncb in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___17
                                                        (fun a18 ->
                                                           let uu___18 =
                                                             unembed e2 a2
                                                               ncb in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___18
                                                             (fun a21 ->
                                                                let uu___19 =
                                                                  unembed e3
                                                                    a3 ncb in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___19
                                                                  (fun a31 ->
                                                                    let uu___20
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a41
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a51
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a61
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a71
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a81
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a91
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a101
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a111
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a121
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a171
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    f a18 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161
                                                                    a171) in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___35
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___34)))))))))))))))))
                                                  | uu___ ->
                                                      FStar_Pervasives_Native.None
let mk_total_interpretation_18 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't2 't3 't4 't5 't6 't7
    't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 -> 't15 -> 't16 -> 't17 -> 't18 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          't18
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            'r
                                              FStarC_Syntax_Embeddings_Base.embedding
                                              ->
                                              FStarC_TypeChecker_Primops_Base.psc
                                                ->
                                                FStarC_Syntax_Embeddings_Base.norm_cb
                                                  ->
                                                  FStarC_Syntax_Syntax.universes
                                                    ->
                                                    FStarC_Syntax_Syntax.args
                                                      ->
                                                      FStarC_Syntax_Syntax.term
                                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun e18 ->
                                          fun er ->
                                            fun psc ->
                                              fun ncb ->
                                                fun us ->
                                                  fun args ->
                                                    match args with
                                                    | (a1, uu___)::(a2,
                                                                    uu___1)::
                                                        (a3, uu___2)::
                                                        (a4, uu___3)::
                                                        (a5, uu___4)::
                                                        (a6, uu___5)::
                                                        (a7, uu___6)::
                                                        (a8, uu___7)::
                                                        (a9, uu___8)::
                                                        (a10, uu___9)::
                                                        (a11, uu___10)::
                                                        (a12, uu___11)::
                                                        (a13, uu___12)::
                                                        (a14, uu___13)::
                                                        (a15, uu___14)::
                                                        (a16, uu___15)::
                                                        (a17, uu___16)::
                                                        (a18, uu___17)::[] ->
                                                        let uu___18 =
                                                          unembed e1 a1 ncb in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___18
                                                          (fun a19 ->
                                                             let uu___19 =
                                                               unembed e2 a2
                                                                 ncb in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___19
                                                               (fun a21 ->
                                                                  let uu___20
                                                                    =
                                                                    unembed
                                                                    e3 a3 ncb in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (
                                                                    fun a31
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a41
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a51
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a61
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a71
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a81
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a91
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a101
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a111
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a121
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a181
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    f a19 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161
                                                                    a171 a181) in
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___37
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___36))))))))))))))))))
                                                    | uu___ ->
                                                        FStar_Pervasives_Native.None
let mk_total_interpretation_19 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't3 't4 't5
    't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 ->
                                   't15 -> 't16 -> 't17 -> 't18 -> 't19 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          't18
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            't19
                                              FStarC_Syntax_Embeddings_Base.embedding
                                              ->
                                              'r
                                                FStarC_Syntax_Embeddings_Base.embedding
                                                ->
                                                FStarC_TypeChecker_Primops_Base.psc
                                                  ->
                                                  FStarC_Syntax_Embeddings_Base.norm_cb
                                                    ->
                                                    FStarC_Syntax_Syntax.universes
                                                      ->
                                                      FStarC_Syntax_Syntax.args
                                                        ->
                                                        FStarC_Syntax_Syntax.term
                                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun e18 ->
                                          fun e19 ->
                                            fun er ->
                                              fun psc ->
                                                fun ncb ->
                                                  fun us ->
                                                    fun args ->
                                                      match args with
                                                      | (a1, uu___)::
                                                          (a2, uu___1)::
                                                          (a3, uu___2)::
                                                          (a4, uu___3)::
                                                          (a5, uu___4)::
                                                          (a6, uu___5)::
                                                          (a7, uu___6)::
                                                          (a8, uu___7)::
                                                          (a9, uu___8)::
                                                          (a10, uu___9)::
                                                          (a11, uu___10)::
                                                          (a12, uu___11)::
                                                          (a13, uu___12)::
                                                          (a14, uu___13)::
                                                          (a15, uu___14)::
                                                          (a16, uu___15)::
                                                          (a17, uu___16)::
                                                          (a18, uu___17)::
                                                          (a19, uu___18)::[]
                                                          ->
                                                          let uu___19 =
                                                            unembed e1 a1 ncb in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___19
                                                            (fun a110 ->
                                                               let uu___20 =
                                                                 unembed e2
                                                                   a2 ncb in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___20
                                                                 (fun a21 ->
                                                                    let uu___21
                                                                    =
                                                                    unembed
                                                                    e3 a3 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a31
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a41
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a51
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a61
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a71
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a81
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a91
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a101
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a111
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a121
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a191
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    f a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191) in
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___39
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___38)))))))))))))))))))
                                                      | uu___ ->
                                                          FStar_Pervasives_Native.None
let mk_total_interpretation_20 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't20 't3 't4
    't5 't6 't7 't8 't9 .
    Prims.string ->
      ('t1 ->
         't2 ->
           't3 ->
             't4 ->
               't5 ->
                 't6 ->
                   't7 ->
                     't8 ->
                       't9 ->
                         't10 ->
                           't11 ->
                             't12 ->
                               't13 ->
                                 't14 ->
                                   't15 ->
                                     't16 ->
                                       't17 -> 't18 -> 't19 -> 't20 -> 'r)
        ->
        't1 FStarC_Syntax_Embeddings_Base.embedding ->
          't2 FStarC_Syntax_Embeddings_Base.embedding ->
            't3 FStarC_Syntax_Embeddings_Base.embedding ->
              't4 FStarC_Syntax_Embeddings_Base.embedding ->
                't5 FStarC_Syntax_Embeddings_Base.embedding ->
                  't6 FStarC_Syntax_Embeddings_Base.embedding ->
                    't7 FStarC_Syntax_Embeddings_Base.embedding ->
                      't8 FStarC_Syntax_Embeddings_Base.embedding ->
                        't9 FStarC_Syntax_Embeddings_Base.embedding ->
                          't10 FStarC_Syntax_Embeddings_Base.embedding ->
                            't11 FStarC_Syntax_Embeddings_Base.embedding ->
                              't12 FStarC_Syntax_Embeddings_Base.embedding ->
                                't13 FStarC_Syntax_Embeddings_Base.embedding
                                  ->
                                  't14
                                    FStarC_Syntax_Embeddings_Base.embedding
                                    ->
                                    't15
                                      FStarC_Syntax_Embeddings_Base.embedding
                                      ->
                                      't16
                                        FStarC_Syntax_Embeddings_Base.embedding
                                        ->
                                        't17
                                          FStarC_Syntax_Embeddings_Base.embedding
                                          ->
                                          't18
                                            FStarC_Syntax_Embeddings_Base.embedding
                                            ->
                                            't19
                                              FStarC_Syntax_Embeddings_Base.embedding
                                              ->
                                              't20
                                                FStarC_Syntax_Embeddings_Base.embedding
                                                ->
                                                'r
                                                  FStarC_Syntax_Embeddings_Base.embedding
                                                  ->
                                                  FStarC_TypeChecker_Primops_Base.psc
                                                    ->
                                                    FStarC_Syntax_Embeddings_Base.norm_cb
                                                      ->
                                                      FStarC_Syntax_Syntax.universes
                                                        ->
                                                        FStarC_Syntax_Syntax.args
                                                          ->
                                                          FStarC_Syntax_Syntax.term
                                                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun f ->
      fun e1 ->
        fun e2 ->
          fun e3 ->
            fun e4 ->
              fun e5 ->
                fun e6 ->
                  fun e7 ->
                    fun e8 ->
                      fun e9 ->
                        fun e10 ->
                          fun e11 ->
                            fun e12 ->
                              fun e13 ->
                                fun e14 ->
                                  fun e15 ->
                                    fun e16 ->
                                      fun e17 ->
                                        fun e18 ->
                                          fun e19 ->
                                            fun e20 ->
                                              fun er ->
                                                fun psc ->
                                                  fun ncb ->
                                                    fun us ->
                                                      fun args ->
                                                        match args with
                                                        | (a1, uu___)::
                                                            (a2, uu___1)::
                                                            (a3, uu___2)::
                                                            (a4, uu___3)::
                                                            (a5, uu___4)::
                                                            (a6, uu___5)::
                                                            (a7, uu___6)::
                                                            (a8, uu___7)::
                                                            (a9, uu___8)::
                                                            (a10, uu___9)::
                                                            (a11, uu___10)::
                                                            (a12, uu___11)::
                                                            (a13, uu___12)::
                                                            (a14, uu___13)::
                                                            (a15, uu___14)::
                                                            (a16, uu___15)::
                                                            (a17, uu___16)::
                                                            (a18, uu___17)::
                                                            (a19, uu___18)::
                                                            (a20, uu___19)::[]
                                                            ->
                                                            let uu___20 =
                                                              unembed e1 a1
                                                                ncb in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___20
                                                              (fun a110 ->
                                                                 let uu___21
                                                                   =
                                                                   unembed e2
                                                                    a2 ncb in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___21
                                                                   (fun a21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    unembed
                                                                    e3 a3 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a31
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    unembed
                                                                    e4 a4 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a41
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    unembed
                                                                    e5 a5 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a51
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    unembed
                                                                    e6 a6 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a61
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    unembed
                                                                    e7 a7 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a71
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e8 a8 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a81
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e9 a9 ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a91
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e10 a10
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a101
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e11 a11
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a111
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e12 a12
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a121
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    unembed
                                                                    e20 a20
                                                                    ncb in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___39
                                                                    (fun a201
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    f a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191
                                                                    a201) in
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___41
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___40))))))))))))))))))))
                                                        | uu___ ->
                                                            FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_1 :
  'r 't1 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            'r FStarC_TypeChecker_NBETerm.embedding ->
              FStarC_Syntax_Syntax.universes ->
                FStarC_TypeChecker_NBETerm.args ->
                  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun er ->
            fun us ->
              fun args ->
                match args with
                | (a1, uu___)::[] ->
                    let uu___1 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                    FStarC_Compiler_Util.bind_opt uu___1
                      (fun a11 ->
                         let r1 = interp_ctx name (fun uu___2 -> f a11) in
                         let uu___2 =
                           FStarC_TypeChecker_NBETerm.embed er cb r1 in
                         FStar_Pervasives_Native.Some uu___2)
                | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_2 :
  'r 't1 't2 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              'r FStarC_TypeChecker_NBETerm.embedding ->
                FStarC_Syntax_Syntax.universes ->
                  FStarC_TypeChecker_NBETerm.args ->
                    FStarC_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun er ->
              fun us ->
                fun args ->
                  match args with
                  | (a1, uu___)::(a2, uu___1)::[] ->
                      let uu___2 =
                        FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                      FStarC_Compiler_Util.bind_opt uu___2
                        (fun a11 ->
                           let uu___3 =
                             FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
                           FStarC_Compiler_Util.bind_opt uu___3
                             (fun a21 ->
                                let r1 =
                                  interp_ctx name (fun uu___4 -> f a11 a21) in
                                let uu___4 =
                                  FStarC_TypeChecker_NBETerm.embed er cb r1 in
                                FStar_Pervasives_Native.Some uu___4))
                  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_3 :
  'r 't1 't2 't3 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                'r FStarC_TypeChecker_NBETerm.embedding ->
                  FStarC_Syntax_Syntax.universes ->
                    FStarC_TypeChecker_NBETerm.args ->
                      FStarC_TypeChecker_NBETerm.t
                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun er ->
                fun us ->
                  fun args ->
                    match args with
                    | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
                        let uu___3 =
                          FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                        FStarC_Compiler_Util.bind_opt uu___3
                          (fun a11 ->
                             let uu___4 =
                               FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
                             FStarC_Compiler_Util.bind_opt uu___4
                               (fun a21 ->
                                  let uu___5 =
                                    FStarC_TypeChecker_NBETerm.unembed e3 cb
                                      a3 in
                                  FStarC_Compiler_Util.bind_opt uu___5
                                    (fun a31 ->
                                       let r1 =
                                         interp_ctx name
                                           (fun uu___6 -> f a11 a21 a31) in
                                       let uu___6 =
                                         FStarC_TypeChecker_NBETerm.embed er
                                           cb r1 in
                                       FStar_Pervasives_Native.Some uu___6)))
                    | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_4 :
  'r 't1 't2 't3 't4 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  'r FStarC_TypeChecker_NBETerm.embedding ->
                    FStarC_Syntax_Syntax.universes ->
                      FStarC_TypeChecker_NBETerm.args ->
                        FStarC_TypeChecker_NBETerm.t
                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun er ->
                  fun us ->
                    fun args ->
                      match args with
                      | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::[]
                          ->
                          let uu___4 =
                            FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                          FStarC_Compiler_Util.bind_opt uu___4
                            (fun a11 ->
                               let uu___5 =
                                 FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
                               FStarC_Compiler_Util.bind_opt uu___5
                                 (fun a21 ->
                                    let uu___6 =
                                      FStarC_TypeChecker_NBETerm.unembed e3
                                        cb a3 in
                                    FStarC_Compiler_Util.bind_opt uu___6
                                      (fun a31 ->
                                         let uu___7 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e4 cb a4 in
                                         FStarC_Compiler_Util.bind_opt uu___7
                                           (fun a41 ->
                                              let r1 =
                                                interp_ctx name
                                                  (fun uu___8 ->
                                                     f a11 a21 a31 a41) in
                                              let uu___8 =
                                                FStarC_TypeChecker_NBETerm.embed
                                                  er cb r1 in
                                              FStar_Pervasives_Native.Some
                                                uu___8))))
                      | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_5 :
  'r 't1 't2 't3 't4 't5 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    'r FStarC_TypeChecker_NBETerm.embedding ->
                      FStarC_Syntax_Syntax.universes ->
                        FStarC_TypeChecker_NBETerm.args ->
                          FStarC_TypeChecker_NBETerm.t
                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun er ->
                    fun us ->
                      fun args ->
                        match args with
                        | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4,
                                                                    uu___3)::
                            (a5, uu___4)::[] ->
                            let uu___5 =
                              FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                            FStarC_Compiler_Util.bind_opt uu___5
                              (fun a11 ->
                                 let uu___6 =
                                   FStarC_TypeChecker_NBETerm.unembed e2 cb
                                     a2 in
                                 FStarC_Compiler_Util.bind_opt uu___6
                                   (fun a21 ->
                                      let uu___7 =
                                        FStarC_TypeChecker_NBETerm.unembed e3
                                          cb a3 in
                                      FStarC_Compiler_Util.bind_opt uu___7
                                        (fun a31 ->
                                           let uu___8 =
                                             FStarC_TypeChecker_NBETerm.unembed
                                               e4 cb a4 in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___8
                                             (fun a41 ->
                                                let uu___9 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    e5 cb a5 in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___9
                                                  (fun a51 ->
                                                     let r1 =
                                                       interp_ctx name
                                                         (fun uu___10 ->
                                                            f a11 a21 a31 a41
                                                              a51) in
                                                     let uu___10 =
                                                       FStarC_TypeChecker_NBETerm.embed
                                                         er cb r1 in
                                                     FStar_Pervasives_Native.Some
                                                       uu___10)))))
                        | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_6 :
  'r 't1 't2 't3 't4 't5 't6 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      'r FStarC_TypeChecker_NBETerm.embedding ->
                        FStarC_Syntax_Syntax.universes ->
                          FStarC_TypeChecker_NBETerm.args ->
                            FStarC_TypeChecker_NBETerm.t
                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun er ->
                      fun us ->
                        fun args ->
                          match args with
                          | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                              (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::[] ->
                              let uu___6 =
                                FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                              FStarC_Compiler_Util.bind_opt uu___6
                                (fun a11 ->
                                   let uu___7 =
                                     FStarC_TypeChecker_NBETerm.unembed e2 cb
                                       a2 in
                                   FStarC_Compiler_Util.bind_opt uu___7
                                     (fun a21 ->
                                        let uu___8 =
                                          FStarC_TypeChecker_NBETerm.unembed
                                            e3 cb a3 in
                                        FStarC_Compiler_Util.bind_opt uu___8
                                          (fun a31 ->
                                             let uu___9 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 e4 cb a4 in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___9
                                               (fun a41 ->
                                                  let uu___10 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      e5 cb a5 in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___10
                                                    (fun a51 ->
                                                       let uu___11 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           e6 cb a6 in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___11
                                                         (fun a61 ->
                                                            let r1 =
                                                              interp_ctx name
                                                                (fun uu___12
                                                                   ->
                                                                   f a11 a21
                                                                    a31 a41
                                                                    a51 a61) in
                                                            let uu___12 =
                                                              FStarC_TypeChecker_NBETerm.embed
                                                                er cb r1 in
                                                            FStar_Pervasives_Native.Some
                                                              uu___12))))))
                          | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_7 :
  'r 't1 't2 't3 't4 't5 't6 't7 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        'r FStarC_TypeChecker_NBETerm.embedding ->
                          FStarC_Syntax_Syntax.universes ->
                            FStarC_TypeChecker_NBETerm.args ->
                              FStarC_TypeChecker_NBETerm.t
                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun er ->
                        fun us ->
                          fun args ->
                            match args with
                            | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                (a7, uu___6)::[] ->
                                let uu___7 =
                                  FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
                                FStarC_Compiler_Util.bind_opt uu___7
                                  (fun a11 ->
                                     let uu___8 =
                                       FStarC_TypeChecker_NBETerm.unembed e2
                                         cb a2 in
                                     FStarC_Compiler_Util.bind_opt uu___8
                                       (fun a21 ->
                                          let uu___9 =
                                            FStarC_TypeChecker_NBETerm.unembed
                                              e3 cb a3 in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___9
                                            (fun a31 ->
                                               let uu___10 =
                                                 FStarC_TypeChecker_NBETerm.unembed
                                                   e4 cb a4 in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___10
                                                 (fun a41 ->
                                                    let uu___11 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        e5 cb a5 in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___11
                                                      (fun a51 ->
                                                         let uu___12 =
                                                           FStarC_TypeChecker_NBETerm.unembed
                                                             e6 cb a6 in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___12
                                                           (fun a61 ->
                                                              let uu___13 =
                                                                FStarC_TypeChecker_NBETerm.unembed
                                                                  e7 cb a7 in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___13
                                                                (fun a71 ->
                                                                   let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71) in
                                                                   let uu___14
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu___14)))))))
                            | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_8 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r) ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          'r FStarC_TypeChecker_NBETerm.embedding ->
                            FStarC_Syntax_Syntax.universes ->
                              FStarC_TypeChecker_NBETerm.args ->
                                FStarC_TypeChecker_NBETerm.t
                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun er ->
                          fun us ->
                            fun args ->
                              match args with
                              | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                  (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                  (a7, uu___6)::(a8, uu___7)::[] ->
                                  let uu___8 =
                                    FStarC_TypeChecker_NBETerm.unembed e1 cb
                                      a1 in
                                  FStarC_Compiler_Util.bind_opt uu___8
                                    (fun a11 ->
                                       let uu___9 =
                                         FStarC_TypeChecker_NBETerm.unembed
                                           e2 cb a2 in
                                       FStarC_Compiler_Util.bind_opt uu___9
                                         (fun a21 ->
                                            let uu___10 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                e3 cb a3 in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___10
                                              (fun a31 ->
                                                 let uu___11 =
                                                   FStarC_TypeChecker_NBETerm.unembed
                                                     e4 cb a4 in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___11
                                                   (fun a41 ->
                                                      let uu___12 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          e5 cb a5 in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___12
                                                        (fun a51 ->
                                                           let uu___13 =
                                                             FStarC_TypeChecker_NBETerm.unembed
                                                               e6 cb a6 in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___13
                                                             (fun a61 ->
                                                                let uu___14 =
                                                                  FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___14
                                                                  (fun a71 ->
                                                                    let uu___15
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___15
                                                                    (fun a81
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81) in
                                                                    let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___16))))))))
                              | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_9 :
  'r 't1 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            'r FStarC_TypeChecker_NBETerm.embedding ->
                              FStarC_Syntax_Syntax.universes ->
                                FStarC_TypeChecker_NBETerm.args ->
                                  FStarC_TypeChecker_NBETerm.t
                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun er ->
                            fun us ->
                              fun args ->
                                match args with
                                | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                    (a4, uu___3)::(a5, uu___4)::(a6, uu___5)::
                                    (a7, uu___6)::(a8, uu___7)::(a9, uu___8)::[]
                                    ->
                                    let uu___9 =
                                      FStarC_TypeChecker_NBETerm.unembed e1
                                        cb a1 in
                                    FStarC_Compiler_Util.bind_opt uu___9
                                      (fun a11 ->
                                         let uu___10 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e2 cb a2 in
                                         FStarC_Compiler_Util.bind_opt
                                           uu___10
                                           (fun a21 ->
                                              let uu___11 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e3 cb a3 in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___11
                                                (fun a31 ->
                                                   let uu___12 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e4 cb a4 in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___12
                                                     (fun a41 ->
                                                        let uu___13 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e5 cb a5 in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___13
                                                          (fun a51 ->
                                                             let uu___14 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e6 cb a6 in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___14
                                                               (fun a61 ->
                                                                  let uu___15
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___15
                                                                    (
                                                                    fun a71
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a81
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a91
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91) in
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___18)))))))))
                                | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_10 :
  'r 't1 't10 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              'r FStarC_TypeChecker_NBETerm.embedding ->
                                FStarC_Syntax_Syntax.universes ->
                                  FStarC_TypeChecker_NBETerm.args ->
                                    FStarC_TypeChecker_NBETerm.t
                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun er ->
                              fun us ->
                                fun args ->
                                  match args with
                                  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                      (a4, uu___3)::(a5, uu___4)::(a6,
                                                                   uu___5)::
                                      (a7, uu___6)::(a8, uu___7)::(a9,
                                                                   uu___8)::
                                      (a10, uu___9)::[] ->
                                      let uu___10 =
                                        FStarC_TypeChecker_NBETerm.unembed e1
                                          cb a1 in
                                      FStarC_Compiler_Util.bind_opt uu___10
                                        (fun a11 ->
                                           let uu___11 =
                                             FStarC_TypeChecker_NBETerm.unembed
                                               e2 cb a2 in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___11
                                             (fun a21 ->
                                                let uu___12 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    e3 cb a3 in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___12
                                                  (fun a31 ->
                                                     let uu___13 =
                                                       FStarC_TypeChecker_NBETerm.unembed
                                                         e4 cb a4 in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___13
                                                       (fun a41 ->
                                                          let uu___14 =
                                                            FStarC_TypeChecker_NBETerm.unembed
                                                              e5 cb a5 in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___14
                                                            (fun a51 ->
                                                               let uu___15 =
                                                                 FStarC_TypeChecker_NBETerm.unembed
                                                                   e6 cb a6 in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___15
                                                                 (fun a61 ->
                                                                    let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___16
                                                                    (fun a71
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a81
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a91
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a101
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    f a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101) in
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___20))))))))))
                                  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_11 :
  'r 't1 't10 't11 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                'r FStarC_TypeChecker_NBETerm.embedding ->
                                  FStarC_Syntax_Syntax.universes ->
                                    FStarC_TypeChecker_NBETerm.args ->
                                      FStarC_TypeChecker_NBETerm.t
                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun er ->
                                fun us ->
                                  fun args ->
                                    match args with
                                    | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::
                                        (a4, uu___3)::(a5, uu___4)::(a6,
                                                                    uu___5)::
                                        (a7, uu___6)::(a8, uu___7)::(a9,
                                                                    uu___8)::
                                        (a10, uu___9)::(a11, uu___10)::[] ->
                                        let uu___11 =
                                          FStarC_TypeChecker_NBETerm.unembed
                                            e1 cb a1 in
                                        FStarC_Compiler_Util.bind_opt uu___11
                                          (fun a12 ->
                                             let uu___12 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 e2 cb a2 in
                                             FStarC_Compiler_Util.bind_opt
                                               uu___12
                                               (fun a21 ->
                                                  let uu___13 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      e3 cb a3 in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___13
                                                    (fun a31 ->
                                                       let uu___14 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           e4 cb a4 in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___14
                                                         (fun a41 ->
                                                            let uu___15 =
                                                              FStarC_TypeChecker_NBETerm.unembed
                                                                e5 cb a5 in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___15
                                                              (fun a51 ->
                                                                 let uu___16
                                                                   =
                                                                   FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___16
                                                                   (fun a61
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a71
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a81
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a91
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a101
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a111
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    f a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111) in
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___22)))))))))))
                                    | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_12 :
  'r 't1 't10 't11 't12 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  'r FStarC_TypeChecker_NBETerm.embedding ->
                                    FStarC_Syntax_Syntax.universes ->
                                      FStarC_TypeChecker_NBETerm.args ->
                                        FStarC_TypeChecker_NBETerm.t
                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun er ->
                                  fun us ->
                                    fun args ->
                                      match args with
                                      | (a1, uu___)::(a2, uu___1)::(a3,
                                                                    uu___2)::
                                          (a4, uu___3)::(a5, uu___4)::
                                          (a6, uu___5)::(a7, uu___6)::
                                          (a8, uu___7)::(a9, uu___8)::
                                          (a10, uu___9)::(a11, uu___10)::
                                          (a12, uu___11)::[] ->
                                          let uu___12 =
                                            FStarC_TypeChecker_NBETerm.unembed
                                              e1 cb a1 in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___12
                                            (fun a13 ->
                                               let uu___13 =
                                                 FStarC_TypeChecker_NBETerm.unembed
                                                   e2 cb a2 in
                                               FStarC_Compiler_Util.bind_opt
                                                 uu___13
                                                 (fun a21 ->
                                                    let uu___14 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        e3 cb a3 in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___14
                                                      (fun a31 ->
                                                         let uu___15 =
                                                           FStarC_TypeChecker_NBETerm.unembed
                                                             e4 cb a4 in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___15
                                                           (fun a41 ->
                                                              let uu___16 =
                                                                FStarC_TypeChecker_NBETerm.unembed
                                                                  e5 cb a5 in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___16
                                                                (fun a51 ->
                                                                   let uu___17
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___17
                                                                    (fun a61
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a71
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a81
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a91
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a101
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a111
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a121
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    f a13 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121) in
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___24))))))))))))
                                      | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_13 :
  'r 't1 't10 't11 't12 't13 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    'r FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      FStarC_Syntax_Syntax.universes ->
                                        FStarC_TypeChecker_NBETerm.args ->
                                          FStarC_TypeChecker_NBETerm.t
                                            FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun er ->
                                    fun us ->
                                      fun args ->
                                        match args with
                                        | (a1, uu___)::(a2, uu___1)::
                                            (a3, uu___2)::(a4, uu___3)::
                                            (a5, uu___4)::(a6, uu___5)::
                                            (a7, uu___6)::(a8, uu___7)::
                                            (a9, uu___8)::(a10, uu___9)::
                                            (a11, uu___10)::(a12, uu___11)::
                                            (a13, uu___12)::[] ->
                                            let uu___13 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                e1 cb a1 in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___13
                                              (fun a14 ->
                                                 let uu___14 =
                                                   FStarC_TypeChecker_NBETerm.unembed
                                                     e2 cb a2 in
                                                 FStarC_Compiler_Util.bind_opt
                                                   uu___14
                                                   (fun a21 ->
                                                      let uu___15 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          e3 cb a3 in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___15
                                                        (fun a31 ->
                                                           let uu___16 =
                                                             FStarC_TypeChecker_NBETerm.unembed
                                                               e4 cb a4 in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___16
                                                             (fun a41 ->
                                                                let uu___17 =
                                                                  FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___17
                                                                  (fun a51 ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (fun a61
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a71
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a81
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a91
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a101
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a111
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a121
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a131
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    f a14 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131) in
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___26)))))))))))))
                                        | uu___ ->
                                            FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_14 :
  'r 't1 't10 't11 't12 't13 't14 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      'r FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        FStarC_Syntax_Syntax.universes ->
                                          FStarC_TypeChecker_NBETerm.args ->
                                            FStarC_TypeChecker_NBETerm.t
                                              FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun er ->
                                      fun us ->
                                        fun args ->
                                          match args with
                                          | (a1, uu___)::(a2, uu___1)::
                                              (a3, uu___2)::(a4, uu___3)::
                                              (a5, uu___4)::(a6, uu___5)::
                                              (a7, uu___6)::(a8, uu___7)::
                                              (a9, uu___8)::(a10, uu___9)::
                                              (a11, uu___10)::(a12, uu___11)::
                                              (a13, uu___12)::(a14, uu___13)::[]
                                              ->
                                              let uu___14 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e1 cb a1 in
                                              FStarC_Compiler_Util.bind_opt
                                                uu___14
                                                (fun a15 ->
                                                   let uu___15 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e2 cb a2 in
                                                   FStarC_Compiler_Util.bind_opt
                                                     uu___15
                                                     (fun a21 ->
                                                        let uu___16 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e3 cb a3 in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___16
                                                          (fun a31 ->
                                                             let uu___17 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e4 cb a4 in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___17
                                                               (fun a41 ->
                                                                  let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___18
                                                                    (
                                                                    fun a51
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a61
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a71
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a81
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a91
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a101
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a111
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a121
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a141
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    f a15 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141) in
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___28))))))))))))))
                                          | uu___ ->
                                              FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_15 :
  'r 't1 't10 't11 't12 't13 't14 't15 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 't15 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        'r
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          FStarC_Syntax_Syntax.universes ->
                                            FStarC_TypeChecker_NBETerm.args
                                              ->
                                              FStarC_TypeChecker_NBETerm.t
                                                FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun er ->
                                        fun us ->
                                          fun args ->
                                            match args with
                                            | (a1, uu___)::(a2, uu___1)::
                                                (a3, uu___2)::(a4, uu___3)::
                                                (a5, uu___4)::(a6, uu___5)::
                                                (a7, uu___6)::(a8, uu___7)::
                                                (a9, uu___8)::(a10, uu___9)::
                                                (a11, uu___10)::(a12,
                                                                 uu___11)::
                                                (a13, uu___12)::(a14,
                                                                 uu___13)::
                                                (a15, uu___14)::[] ->
                                                let uu___15 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    e1 cb a1 in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___15
                                                  (fun a16 ->
                                                     let uu___16 =
                                                       FStarC_TypeChecker_NBETerm.unembed
                                                         e2 cb a2 in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___16
                                                       (fun a21 ->
                                                          let uu___17 =
                                                            FStarC_TypeChecker_NBETerm.unembed
                                                              e3 cb a3 in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___17
                                                            (fun a31 ->
                                                               let uu___18 =
                                                                 FStarC_TypeChecker_NBETerm.unembed
                                                                   e4 cb a4 in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___18
                                                                 (fun a41 ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___19
                                                                    (fun a51
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a61
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a71
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a81
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a91
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a101
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a111
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a121
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a151
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    f a16 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151) in
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___30)))))))))))))))
                                            | uu___ ->
                                                FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_16 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't2 't3 't4 't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 -> 't13 -> 't14 -> 't15 -> 't16 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          'r
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            FStarC_Syntax_Syntax.universes ->
                                              FStarC_TypeChecker_NBETerm.args
                                                ->
                                                FStarC_TypeChecker_NBETerm.t
                                                  FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun er ->
                                          fun us ->
                                            fun args ->
                                              match args with
                                              | (a1, uu___)::(a2, uu___1)::
                                                  (a3, uu___2)::(a4, uu___3)::
                                                  (a5, uu___4)::(a6, uu___5)::
                                                  (a7, uu___6)::(a8, uu___7)::
                                                  (a9, uu___8)::(a10, uu___9)::
                                                  (a11, uu___10)::(a12,
                                                                   uu___11)::
                                                  (a13, uu___12)::(a14,
                                                                   uu___13)::
                                                  (a15, uu___14)::(a16,
                                                                   uu___15)::[]
                                                  ->
                                                  let uu___16 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      e1 cb a1 in
                                                  FStarC_Compiler_Util.bind_opt
                                                    uu___16
                                                    (fun a17 ->
                                                       let uu___17 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           e2 cb a2 in
                                                       FStarC_Compiler_Util.bind_opt
                                                         uu___17
                                                         (fun a21 ->
                                                            let uu___18 =
                                                              FStarC_TypeChecker_NBETerm.unembed
                                                                e3 cb a3 in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___18
                                                              (fun a31 ->
                                                                 let uu___19
                                                                   =
                                                                   FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                 FStarC_Compiler_Util.bind_opt
                                                                   uu___19
                                                                   (fun a41
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a51
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a61
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a71
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a81
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a91
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a101
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a111
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a121
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a161
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    f a17 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161) in
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___32))))))))))))))))
                                              | uu___ ->
                                                  FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_17 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't2 't3 't4 't5 't6 't7 't8
    't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 -> 't14 -> 't15 -> 't16 -> 't17 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            'r
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              FStarC_Syntax_Syntax.universes
                                                ->
                                                FStarC_TypeChecker_NBETerm.args
                                                  ->
                                                  FStarC_TypeChecker_NBETerm.t
                                                    FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun er ->
                                            fun us ->
                                              fun args ->
                                                match args with
                                                | (a1, uu___)::(a2, uu___1)::
                                                    (a3, uu___2)::(a4,
                                                                   uu___3)::
                                                    (a5, uu___4)::(a6,
                                                                   uu___5)::
                                                    (a7, uu___6)::(a8,
                                                                   uu___7)::
                                                    (a9, uu___8)::(a10,
                                                                   uu___9)::
                                                    (a11, uu___10)::(a12,
                                                                    uu___11)::
                                                    (a13, uu___12)::(a14,
                                                                    uu___13)::
                                                    (a15, uu___14)::(a16,
                                                                    uu___15)::
                                                    (a17, uu___16)::[] ->
                                                    let uu___17 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        e1 cb a1 in
                                                    FStarC_Compiler_Util.bind_opt
                                                      uu___17
                                                      (fun a18 ->
                                                         let uu___18 =
                                                           FStarC_TypeChecker_NBETerm.unembed
                                                             e2 cb a2 in
                                                         FStarC_Compiler_Util.bind_opt
                                                           uu___18
                                                           (fun a21 ->
                                                              let uu___19 =
                                                                FStarC_TypeChecker_NBETerm.unembed
                                                                  e3 cb a3 in
                                                              FStarC_Compiler_Util.bind_opt
                                                                uu___19
                                                                (fun a31 ->
                                                                   let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                   FStarC_Compiler_Util.bind_opt
                                                                    uu___20
                                                                    (fun a41
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a51
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a61
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a71
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a81
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a91
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a101
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a111
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a121
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a171
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    f a18 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161
                                                                    a171) in
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___34)))))))))))))))))
                                                | uu___ ->
                                                    FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_18 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't2 't3 't4 't5 't6 't7
    't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 -> 't15 -> 't16 -> 't17 -> 't18 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            't18
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              'r
                                                FStarC_TypeChecker_NBETerm.embedding
                                                ->
                                                FStarC_Syntax_Syntax.universes
                                                  ->
                                                  FStarC_TypeChecker_NBETerm.args
                                                    ->
                                                    FStarC_TypeChecker_NBETerm.t
                                                      FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun e18 ->
                                            fun er ->
                                              fun us ->
                                                fun args ->
                                                  match args with
                                                  | (a1, uu___)::(a2, uu___1)::
                                                      (a3, uu___2)::(a4,
                                                                    uu___3)::
                                                      (a5, uu___4)::(a6,
                                                                    uu___5)::
                                                      (a7, uu___6)::(a8,
                                                                    uu___7)::
                                                      (a9, uu___8)::(a10,
                                                                    uu___9)::
                                                      (a11, uu___10)::
                                                      (a12, uu___11)::
                                                      (a13, uu___12)::
                                                      (a14, uu___13)::
                                                      (a15, uu___14)::
                                                      (a16, uu___15)::
                                                      (a17, uu___16)::
                                                      (a18, uu___17)::[] ->
                                                      let uu___18 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          e1 cb a1 in
                                                      FStarC_Compiler_Util.bind_opt
                                                        uu___18
                                                        (fun a19 ->
                                                           let uu___19 =
                                                             FStarC_TypeChecker_NBETerm.unembed
                                                               e2 cb a2 in
                                                           FStarC_Compiler_Util.bind_opt
                                                             uu___19
                                                             (fun a21 ->
                                                                let uu___20 =
                                                                  FStarC_TypeChecker_NBETerm.unembed
                                                                    e3 cb a3 in
                                                                FStarC_Compiler_Util.bind_opt
                                                                  uu___20
                                                                  (fun a31 ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (fun a41
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a51
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a61
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a71
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a81
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a91
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a101
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a111
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a121
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a181
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    f a19 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161
                                                                    a171 a181) in
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___36))))))))))))))))))
                                                  | uu___ ->
                                                      FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_19 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't3 't4 't5
    't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 ->
                                       't16 -> 't17 -> 't18 -> 't19 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            't18
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              't19
                                                FStarC_TypeChecker_NBETerm.embedding
                                                ->
                                                'r
                                                  FStarC_TypeChecker_NBETerm.embedding
                                                  ->
                                                  FStarC_Syntax_Syntax.universes
                                                    ->
                                                    FStarC_TypeChecker_NBETerm.args
                                                      ->
                                                      FStarC_TypeChecker_NBETerm.t
                                                        FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun e18 ->
                                            fun e19 ->
                                              fun er ->
                                                fun us ->
                                                  fun args ->
                                                    match args with
                                                    | (a1, uu___)::(a2,
                                                                    uu___1)::
                                                        (a3, uu___2)::
                                                        (a4, uu___3)::
                                                        (a5, uu___4)::
                                                        (a6, uu___5)::
                                                        (a7, uu___6)::
                                                        (a8, uu___7)::
                                                        (a9, uu___8)::
                                                        (a10, uu___9)::
                                                        (a11, uu___10)::
                                                        (a12, uu___11)::
                                                        (a13, uu___12)::
                                                        (a14, uu___13)::
                                                        (a15, uu___14)::
                                                        (a16, uu___15)::
                                                        (a17, uu___16)::
                                                        (a18, uu___17)::
                                                        (a19, uu___18)::[] ->
                                                        let uu___19 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e1 cb a1 in
                                                        FStarC_Compiler_Util.bind_opt
                                                          uu___19
                                                          (fun a110 ->
                                                             let uu___20 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e2 cb a2 in
                                                             FStarC_Compiler_Util.bind_opt
                                                               uu___20
                                                               (fun a21 ->
                                                                  let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e3 cb a3 in
                                                                  FStarC_Compiler_Util.bind_opt
                                                                    uu___21
                                                                    (
                                                                    fun a31
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a41
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a51
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a61
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a71
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a81
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a91
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a101
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a111
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a121
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a191
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    f a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191) in
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___38)))))))))))))))))))
                                                    | uu___ ->
                                                        FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_20 :
  'r 't1 't10 't11 't12 't13 't14 't15 't16 't17 't18 't19 't2 't20 't3 't4
    't5 't6 't7 't8 't9 .
    Prims.string ->
      FStarC_TypeChecker_NBETerm.nbe_cbs ->
        ('t1 ->
           't2 ->
             't3 ->
               't4 ->
                 't5 ->
                   't6 ->
                     't7 ->
                       't8 ->
                         't9 ->
                           't10 ->
                             't11 ->
                               't12 ->
                                 't13 ->
                                   't14 ->
                                     't15 ->
                                       't16 ->
                                         't17 -> 't18 -> 't19 -> 't20 -> 'r)
          ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            't2 FStarC_TypeChecker_NBETerm.embedding ->
              't3 FStarC_TypeChecker_NBETerm.embedding ->
                't4 FStarC_TypeChecker_NBETerm.embedding ->
                  't5 FStarC_TypeChecker_NBETerm.embedding ->
                    't6 FStarC_TypeChecker_NBETerm.embedding ->
                      't7 FStarC_TypeChecker_NBETerm.embedding ->
                        't8 FStarC_TypeChecker_NBETerm.embedding ->
                          't9 FStarC_TypeChecker_NBETerm.embedding ->
                            't10 FStarC_TypeChecker_NBETerm.embedding ->
                              't11 FStarC_TypeChecker_NBETerm.embedding ->
                                't12 FStarC_TypeChecker_NBETerm.embedding ->
                                  't13 FStarC_TypeChecker_NBETerm.embedding
                                    ->
                                    't14 FStarC_TypeChecker_NBETerm.embedding
                                      ->
                                      't15
                                        FStarC_TypeChecker_NBETerm.embedding
                                        ->
                                        't16
                                          FStarC_TypeChecker_NBETerm.embedding
                                          ->
                                          't17
                                            FStarC_TypeChecker_NBETerm.embedding
                                            ->
                                            't18
                                              FStarC_TypeChecker_NBETerm.embedding
                                              ->
                                              't19
                                                FStarC_TypeChecker_NBETerm.embedding
                                                ->
                                                't20
                                                  FStarC_TypeChecker_NBETerm.embedding
                                                  ->
                                                  'r
                                                    FStarC_TypeChecker_NBETerm.embedding
                                                    ->
                                                    FStarC_Syntax_Syntax.universes
                                                      ->
                                                      FStarC_TypeChecker_NBETerm.args
                                                        ->
                                                        FStarC_TypeChecker_NBETerm.t
                                                          FStar_Pervasives_Native.option
  =
  fun name ->
    fun cb ->
      fun f ->
        fun e1 ->
          fun e2 ->
            fun e3 ->
              fun e4 ->
                fun e5 ->
                  fun e6 ->
                    fun e7 ->
                      fun e8 ->
                        fun e9 ->
                          fun e10 ->
                            fun e11 ->
                              fun e12 ->
                                fun e13 ->
                                  fun e14 ->
                                    fun e15 ->
                                      fun e16 ->
                                        fun e17 ->
                                          fun e18 ->
                                            fun e19 ->
                                              fun e20 ->
                                                fun er ->
                                                  fun us ->
                                                    fun args ->
                                                      match args with
                                                      | (a1, uu___)::
                                                          (a2, uu___1)::
                                                          (a3, uu___2)::
                                                          (a4, uu___3)::
                                                          (a5, uu___4)::
                                                          (a6, uu___5)::
                                                          (a7, uu___6)::
                                                          (a8, uu___7)::
                                                          (a9, uu___8)::
                                                          (a10, uu___9)::
                                                          (a11, uu___10)::
                                                          (a12, uu___11)::
                                                          (a13, uu___12)::
                                                          (a14, uu___13)::
                                                          (a15, uu___14)::
                                                          (a16, uu___15)::
                                                          (a17, uu___16)::
                                                          (a18, uu___17)::
                                                          (a19, uu___18)::
                                                          (a20, uu___19)::[]
                                                          ->
                                                          let uu___20 =
                                                            FStarC_TypeChecker_NBETerm.unembed
                                                              e1 cb a1 in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___20
                                                            (fun a110 ->
                                                               let uu___21 =
                                                                 FStarC_TypeChecker_NBETerm.unembed
                                                                   e2 cb a2 in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___21
                                                                 (fun a21 ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e3 cb a3 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___22
                                                                    (fun a31
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e4 cb a4 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___23
                                                                    (fun a41
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e5 cb a5 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___24
                                                                    (fun a51
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e6 cb a6 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___25
                                                                    (fun a61
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e7 cb a7 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___26
                                                                    (fun a71
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e8 cb a8 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___27
                                                                    (fun a81
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e9 cb a9 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___28
                                                                    (fun a91
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e10 cb
                                                                    a10 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___29
                                                                    (fun a101
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e11 cb
                                                                    a11 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___30
                                                                    (fun a111
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e12 cb
                                                                    a12 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___31
                                                                    (fun a121
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___32
                                                                    (fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e20 cb
                                                                    a20 in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___39
                                                                    (fun a201
                                                                    ->
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    f a110
                                                                    a21 a31
                                                                    a41 a51
                                                                    a61 a71
                                                                    a81 a91
                                                                    a101 a111
                                                                    a121 a131
                                                                    a141 a151
                                                                    a161 a171
                                                                    a181 a191
                                                                    a201) in
                                                                    let uu___40
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___40))))))))))))))))))))
                                                      | uu___ ->
                                                          FStar_Pervasives_Native.None