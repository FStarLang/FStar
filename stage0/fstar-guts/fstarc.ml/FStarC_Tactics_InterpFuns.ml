open Prims
let solve (ev : 'a) : 'a= ev
let embed (e : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (rng : FStarC_Range_Type.t) (t : 'a)
  (n : FStarC_Syntax_Embeddings_Base.norm_cb) : FStarC_Syntax_Syntax.term=
  let uu___ = FStarC_Syntax_Embeddings_Base.embed e t in
  uu___ rng FStar_Pervasives_Native.None n
let unembed (e : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (t : FStarC_Syntax_Syntax.term) (n : FStarC_Syntax_Embeddings_Base.norm_cb)
  : 'a FStar_Pervasives_Native.option=
  FStarC_Syntax_Embeddings_Base.unembed e t n
let interp_ctx (s : Prims.string) (f : unit -> 'a) : 'a=
  FStarC_Errors.with_ctx (Prims.strcat "While running primitive " s) f
let run_wrap (label : Prims.string) (t : 'a FStarC_Tactics_Monad.tac)
  (ps : FStarC_Tactics_Types.proofstate FStarC_Effect.ref) : 'a=
  interp_ctx label (fun uu___ -> t ps)
let builtin_lid (nm : Prims.string) : FStarC_Ident.lid=
  FStarC_Parser_Const.fstar_stubs_tactics_lid' ["V2"; "Builtins"; nm]
let types_lid (nm : Prims.string) : FStarC_Ident.lid=
  FStarC_Parser_Const.fstar_stubs_tactics_lid' ["Types"; nm]
let set_auto_reflect (arity : Prims.int)
  (p : FStarC_TypeChecker_Primops_Base.primitive_step) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
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
let mk_tot_step_1 (uarity : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___3 : 'nres FStarC_TypeChecker_NBETerm.embedding) (f : 't1 -> 'res)
  (nbe_f : 'nt1 -> 'nres) : FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = types_lid nm in
  FStarC_TypeChecker_Primops_Base.mk1' uarity lid uu___ uu___2 uu___1 uu___3
    (fun x -> let uu___4 = f x in FStar_Pervasives_Native.Some uu___4)
    (fun x -> let uu___4 = nbe_f x in FStar_Pervasives_Native.Some uu___4)
let mk_tot_step_2 (uarity : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'nt2 FStarC_TypeChecker_NBETerm.embedding)
  (uu___5 : 'nres FStarC_TypeChecker_NBETerm.embedding)
  (f : 't1 -> 't2 -> 'res) (nbe_f : 'nt1 -> 'nt2 -> 'nres) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = types_lid nm in
  FStarC_TypeChecker_Primops_Base.mk2' uarity lid uu___ uu___3 uu___1 uu___4
    uu___2 uu___5
    (fun x y -> let uu___6 = f x y in FStar_Pervasives_Native.Some uu___6)
    (fun x y -> let uu___6 = nbe_f x y in FStar_Pervasives_Native.Some uu___6)
let mk_tot_step_1_psc (us : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___3 : 'nres FStarC_TypeChecker_NBETerm.embedding)
  (f : FStarC_TypeChecker_Primops_Base.psc -> 't1 -> 'res)
  (nbe_f : FStarC_TypeChecker_Primops_Base.psc -> 'nt1 -> 'nres) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = types_lid nm in
  FStarC_TypeChecker_Primops_Base.mk1_psc' us lid uu___ uu___2 uu___1 uu___3
    (fun psc x -> let uu___4 = f psc x in FStar_Pervasives_Native.Some uu___4)
    (fun psc x ->
       let uu___4 = nbe_f psc x in FStar_Pervasives_Native.Some uu___4)
let mk_tac_step_1 (univ_arity : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___3 : 'nres FStarC_TypeChecker_NBETerm.embedding)
  (f : 't1 -> 'res FStarC_Tactics_Monad.tac)
  (nbe_f : 'nt1 -> 'nres FStarC_Tactics_Monad.tac) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = builtin_lid nm in
  let uu___4 =
    FStarC_TypeChecker_Primops_Base.mk2' univ_arity lid uu___ uu___2
      FStarC_Tactics_Embedding.e_ref_proofstate
      FStarC_Tactics_Embedding.e_ref_proofstate_nbe uu___1 uu___3
      (fun a ps ->
         let uu___5 = let uu___6 = f a in run_wrap nm uu___6 ps in
         FStar_Pervasives_Native.Some uu___5)
      (fun a ps ->
         let uu___5 = let uu___6 = nbe_f a in run_wrap nm uu___6 ps in
         FStar_Pervasives_Native.Some uu___5) in
  set_auto_reflect Prims.int_one uu___4
let mk_tac_step_2 (univ_arity : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'nt2 FStarC_TypeChecker_NBETerm.embedding)
  (uu___5 : 'nres FStarC_TypeChecker_NBETerm.embedding)
  (f : 't1 -> 't2 -> 'res FStarC_Tactics_Monad.tac)
  (nbe_f : 'nt1 -> 'nt2 -> 'nres FStarC_Tactics_Monad.tac) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = builtin_lid nm in
  let uu___6 =
    FStarC_TypeChecker_Primops_Base.mk3' univ_arity lid uu___ uu___3 uu___1
      uu___4 FStarC_Tactics_Embedding.e_ref_proofstate
      FStarC_Tactics_Embedding.e_ref_proofstate_nbe uu___2 uu___5
      (fun a b ps ->
         let uu___7 = let uu___8 = f a b in run_wrap nm uu___8 ps in
         FStar_Pervasives_Native.Some uu___7)
      (fun a b ps ->
         let uu___7 = let uu___8 = nbe_f a b in run_wrap nm uu___8 ps in
         FStar_Pervasives_Native.Some uu___7) in
  set_auto_reflect (Prims.of_int (2)) uu___6
let mk_tac_step_3 (univ_arity : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___4 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___5 : 'nt2 FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'nt3 FStarC_TypeChecker_NBETerm.embedding)
  (uu___7 : 'nres FStarC_TypeChecker_NBETerm.embedding)
  (f : 't1 -> 't2 -> 't3 -> 'res FStarC_Tactics_Monad.tac)
  (nbe_f : 'nt1 -> 'nt2 -> 'nt3 -> 'nres FStarC_Tactics_Monad.tac) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = builtin_lid nm in
  let uu___8 =
    FStarC_TypeChecker_Primops_Base.mk4' univ_arity lid uu___ uu___4 uu___1
      uu___5 uu___2 uu___6 FStarC_Tactics_Embedding.e_ref_proofstate
      FStarC_Tactics_Embedding.e_ref_proofstate_nbe uu___3 uu___7
      (fun a b c ps ->
         let uu___9 = let uu___10 = f a b c in run_wrap nm uu___10 ps in
         FStar_Pervasives_Native.Some uu___9)
      (fun a b c ps ->
         let uu___9 = let uu___10 = nbe_f a b c in run_wrap nm uu___10 ps in
         FStar_Pervasives_Native.Some uu___9) in
  set_auto_reflect (Prims.of_int (3)) uu___8
let mk_tac_step_4 (univ_arity : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___4 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'nt2 FStarC_TypeChecker_NBETerm.embedding)
  (uu___7 : 'nt3 FStarC_TypeChecker_NBETerm.embedding)
  (uu___8 : 'nt4 FStarC_TypeChecker_NBETerm.embedding)
  (uu___9 : 'nres FStarC_TypeChecker_NBETerm.embedding)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 'res FStarC_Tactics_Monad.tac)
  (nbe_f : 'nt1 -> 'nt2 -> 'nt3 -> 'nt4 -> 'nres FStarC_Tactics_Monad.tac) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = builtin_lid nm in
  let uu___10 =
    FStarC_TypeChecker_Primops_Base.mk5' univ_arity lid uu___ uu___5 uu___1
      uu___6 uu___2 uu___7 uu___3 uu___8
      FStarC_Tactics_Embedding.e_ref_proofstate
      FStarC_Tactics_Embedding.e_ref_proofstate_nbe uu___4 uu___9
      (fun a b c d ps ->
         let uu___11 = let uu___12 = f a b c d in run_wrap nm uu___12 ps in
         FStar_Pervasives_Native.Some uu___11)
      (fun a b c d ps ->
         let uu___11 = let uu___12 = nbe_f a b c d in run_wrap nm uu___12 ps in
         FStar_Pervasives_Native.Some uu___11) in
  set_auto_reflect (Prims.of_int (4)) uu___10
let mk_tac_step_5 (univ_arity : Prims.int) (nm : Prims.string)
  (uu___ : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___4 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'res FStarC_Syntax_Embeddings_Base.embedding)
  (uu___6 : 'nt1 FStarC_TypeChecker_NBETerm.embedding)
  (uu___7 : 'nt2 FStarC_TypeChecker_NBETerm.embedding)
  (uu___8 : 'nt3 FStarC_TypeChecker_NBETerm.embedding)
  (uu___9 : 'nt4 FStarC_TypeChecker_NBETerm.embedding)
  (uu___10 : 'nt5 FStarC_TypeChecker_NBETerm.embedding)
  (uu___11 : 'nres FStarC_TypeChecker_NBETerm.embedding)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'res FStarC_Tactics_Monad.tac)
  (nbe_f :
    'nt1 -> 'nt2 -> 'nt3 -> 'nt4 -> 'nt5 -> 'nres FStarC_Tactics_Monad.tac)
  : FStarC_TypeChecker_Primops_Base.primitive_step=
  let lid = builtin_lid nm in
  let uu___12 =
    FStarC_TypeChecker_Primops_Base.mk6' univ_arity lid uu___ uu___6 uu___1
      uu___7 uu___2 uu___8 uu___3 uu___9 uu___4 uu___10
      FStarC_Tactics_Embedding.e_ref_proofstate
      FStarC_Tactics_Embedding.e_ref_proofstate_nbe uu___5 uu___11
      (fun a b c d e ps ->
         let uu___13 = let uu___14 = f a b c d e in run_wrap nm uu___14 ps in
         FStar_Pervasives_Native.Some uu___13)
      (fun a b c d e ps ->
         let uu___13 =
           let uu___14 = nbe_f a b c d e in run_wrap nm uu___14 ps in
         FStar_Pervasives_Native.Some uu___13) in
  set_auto_reflect (Prims.of_int (5)) uu___12
let max_tac_arity : Prims.int= (Prims.of_int (20))
let mk_tactic_interpretation_1 (name : Prims.string)
  (t : 't1 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::[] ->
      let uu___2 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___2
        (fun a11 ->
           let uu___3 =
             unembed FStarC_Tactics_Embedding.e_ref_proofstate a2 ncb in
           FStarC_Option.bind uu___3
             (fun ps ->
                (let uu___5 =
                   let uu___6 = FStarC_Effect.op_Bang ps in
                   FStarC_Tactics_Types.set_ps_psc psc uu___6 in
                 FStarC_Effect.op_Colon_Equals ps uu___5);
                (let r1 =
                   interp_ctx name
                     (fun uu___5 -> let uu___6 = t a11 in uu___6 ps) in
                 let uu___5 =
                   let uu___6 = FStarC_TypeChecker_Primops_Base.psc_range psc in
                   embed er uu___6 r1 ncb in
                 FStar_Pervasives_Native.Some uu___5)))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_2 (name : Prims.string)
  (t : 't1 -> 't2 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
      let uu___3 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___3
        (fun a11 ->
           let uu___4 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___4
             (fun a21 ->
                let uu___5 =
                  unembed FStarC_Tactics_Embedding.e_ref_proofstate a3 ncb in
                FStarC_Option.bind uu___5
                  (fun ps ->
                     (let uu___7 =
                        let uu___8 = FStarC_Effect.op_Bang ps in
                        FStarC_Tactics_Types.set_ps_psc psc uu___8 in
                      FStarC_Effect.op_Colon_Equals ps uu___7);
                     (let r1 =
                        interp_ctx name
                          (fun uu___7 -> let uu___8 = t a11 a21 in uu___8 ps) in
                      let uu___7 =
                        let uu___8 =
                          FStarC_TypeChecker_Primops_Base.psc_range psc in
                        embed er uu___8 r1 ncb in
                      FStar_Pervasives_Native.Some uu___7))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_3 (name : Prims.string)
  (t : 't1 -> 't2 -> 't3 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::[] ->
      let uu___4 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___4
        (fun a11 ->
           let uu___5 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___5
             (fun a21 ->
                let uu___6 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___6
                  (fun a31 ->
                     let uu___7 =
                       unembed FStarC_Tactics_Embedding.e_ref_proofstate a4
                         ncb in
                     FStarC_Option.bind uu___7
                       (fun ps ->
                          (let uu___9 =
                             let uu___10 = FStarC_Effect.op_Bang ps in
                             FStarC_Tactics_Types.set_ps_psc psc uu___10 in
                           FStarC_Effect.op_Colon_Equals ps uu___9);
                          (let r1 =
                             interp_ctx name
                               (fun uu___9 ->
                                  let uu___10 = t a11 a21 a31 in uu___10 ps) in
                           let uu___9 =
                             let uu___10 =
                               FStarC_TypeChecker_Primops_Base.psc_range psc in
                             embed er uu___10 r1 ncb in
                           FStar_Pervasives_Native.Some uu___9)))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_4 (name : Prims.string)
  (t : 't1 -> 't2 -> 't3 -> 't4 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::[]
      ->
      let uu___5 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___5
        (fun a11 ->
           let uu___6 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___6
             (fun a21 ->
                let uu___7 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___7
                  (fun a31 ->
                     let uu___8 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___8
                       (fun a41 ->
                          let uu___9 =
                            unembed FStarC_Tactics_Embedding.e_ref_proofstate
                              a5 ncb in
                          FStarC_Option.bind uu___9
                            (fun ps ->
                               (let uu___11 =
                                  let uu___12 = FStarC_Effect.op_Bang ps in
                                  FStarC_Tactics_Types.set_ps_psc psc uu___12 in
                                FStarC_Effect.op_Colon_Equals ps uu___11);
                               (let r1 =
                                  interp_ctx name
                                    (fun uu___11 ->
                                       let uu___12 = t a11 a21 a31 a41 in
                                       uu___12 ps) in
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_TypeChecker_Primops_Base.psc_range
                                      psc in
                                  embed er uu___12 r1 ncb in
                                FStar_Pervasives_Native.Some uu___11))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_5 (name : Prims.string)
  (t : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::[] ->
      let uu___6 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___6
        (fun a11 ->
           let uu___7 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___7
             (fun a21 ->
                let uu___8 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___8
                  (fun a31 ->
                     let uu___9 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___9
                       (fun a41 ->
                          let uu___10 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___10
                            (fun a51 ->
                               let uu___11 =
                                 unembed
                                   FStarC_Tactics_Embedding.e_ref_proofstate
                                   a6 ncb in
                               FStarC_Option.bind uu___11
                                 (fun ps ->
                                    (let uu___13 =
                                       let uu___14 = FStarC_Effect.op_Bang ps in
                                       FStarC_Tactics_Types.set_ps_psc psc
                                         uu___14 in
                                     FStarC_Effect.op_Colon_Equals ps uu___13);
                                    (let r1 =
                                       interp_ctx name
                                         (fun uu___13 ->
                                            let uu___14 =
                                              t a11 a21 a31 a41 a51 in
                                            uu___14 ps) in
                                     let uu___13 =
                                       let uu___14 =
                                         FStarC_TypeChecker_Primops_Base.psc_range
                                           psc in
                                       embed er uu___14 r1 ncb in
                                     FStar_Pervasives_Native.Some uu___13)))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_6 (name : Prims.string)
  (t : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::[] ->
      let uu___7 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___7
        (fun a11 ->
           let uu___8 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___8
             (fun a21 ->
                let uu___9 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___9
                  (fun a31 ->
                     let uu___10 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___10
                       (fun a41 ->
                          let uu___11 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___11
                            (fun a51 ->
                               let uu___12 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___12
                                 (fun a61 ->
                                    let uu___13 =
                                      unembed
                                        FStarC_Tactics_Embedding.e_ref_proofstate
                                        a7 ncb in
                                    FStarC_Option.bind uu___13
                                      (fun ps ->
                                         (let uu___15 =
                                            let uu___16 =
                                              FStarC_Effect.op_Bang ps in
                                            FStarC_Tactics_Types.set_ps_psc
                                              psc uu___16 in
                                          FStarC_Effect.op_Colon_Equals ps
                                            uu___15);
                                         (let r1 =
                                            interp_ctx name
                                              (fun uu___15 ->
                                                 let uu___16 =
                                                   t a11 a21 a31 a41 a51 a61 in
                                                 uu___16 ps) in
                                          let uu___15 =
                                            let uu___16 =
                                              FStarC_TypeChecker_Primops_Base.psc_range
                                                psc in
                                            embed er uu___16 r1 ncb in
                                          FStar_Pervasives_Native.Some
                                            uu___15))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_7 (name : Prims.string)
  (t :
    't1 ->
      't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::[] ->
      let uu___8 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___8
        (fun a11 ->
           let uu___9 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___9
             (fun a21 ->
                let uu___10 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___10
                  (fun a31 ->
                     let uu___11 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___11
                       (fun a41 ->
                          let uu___12 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___12
                            (fun a51 ->
                               let uu___13 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___13
                                 (fun a61 ->
                                    let uu___14 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___14
                                      (fun a71 ->
                                         let uu___15 =
                                           unembed
                                             FStarC_Tactics_Embedding.e_ref_proofstate
                                             a8 ncb in
                                         FStarC_Option.bind uu___15
                                           (fun ps ->
                                              (let uu___17 =
                                                 let uu___18 =
                                                   FStarC_Effect.op_Bang ps in
                                                 FStarC_Tactics_Types.set_ps_psc
                                                   psc uu___18 in
                                               FStarC_Effect.op_Colon_Equals
                                                 ps uu___17);
                                              (let r1 =
                                                 interp_ctx name
                                                   (fun uu___17 ->
                                                      let uu___18 =
                                                        t a11 a21 a31 a41 a51
                                                          a61 a71 in
                                                      uu___18 ps) in
                                               let uu___17 =
                                                 let uu___18 =
                                                   FStarC_TypeChecker_Primops_Base.psc_range
                                                     psc in
                                                 embed er uu___18 r1 ncb in
                                               FStar_Pervasives_Native.Some
                                                 uu___17)))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_8 (name : Prims.string)
  (t :
    't1 ->
      't2 ->
        't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::[] ->
      let uu___9 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___9
        (fun a11 ->
           let uu___10 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___10
             (fun a21 ->
                let uu___11 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___11
                  (fun a31 ->
                     let uu___12 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___12
                       (fun a41 ->
                          let uu___13 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___13
                            (fun a51 ->
                               let uu___14 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___14
                                 (fun a61 ->
                                    let uu___15 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___15
                                      (fun a71 ->
                                         let uu___16 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___16
                                           (fun a81 ->
                                              let uu___17 =
                                                unembed
                                                  FStarC_Tactics_Embedding.e_ref_proofstate
                                                  a9 ncb in
                                              FStarC_Option.bind uu___17
                                                (fun ps ->
                                                   (let uu___19 =
                                                      let uu___20 =
                                                        FStarC_Effect.op_Bang
                                                          ps in
                                                      FStarC_Tactics_Types.set_ps_psc
                                                        psc uu___20 in
                                                    FStarC_Effect.op_Colon_Equals
                                                      ps uu___19);
                                                   (let r1 =
                                                      interp_ctx name
                                                        (fun uu___19 ->
                                                           let uu___20 =
                                                             t a11 a21 a31
                                                               a41 a51 a61
                                                               a71 a81 in
                                                           uu___20 ps) in
                                                    let uu___19 =
                                                      let uu___20 =
                                                        FStarC_TypeChecker_Primops_Base.psc_range
                                                          psc in
                                                      embed er uu___20 r1 ncb in
                                                    FStar_Pervasives_Native.Some
                                                      uu___19))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_9 (name : Prims.string)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::[]
      ->
      let uu___10 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___10
        (fun a11 ->
           let uu___11 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___11
             (fun a21 ->
                let uu___12 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___12
                  (fun a31 ->
                     let uu___13 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___13
                       (fun a41 ->
                          let uu___14 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___14
                            (fun a51 ->
                               let uu___15 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___15
                                 (fun a61 ->
                                    let uu___16 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___16
                                      (fun a71 ->
                                         let uu___17 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___17
                                           (fun a81 ->
                                              let uu___18 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___18
                                                (fun a91 ->
                                                   let uu___19 =
                                                     unembed
                                                       FStarC_Tactics_Embedding.e_ref_proofstate
                                                       a10 ncb in
                                                   FStarC_Option.bind uu___19
                                                     (fun ps ->
                                                        (let uu___21 =
                                                           let uu___22 =
                                                             FStarC_Effect.op_Bang
                                                               ps in
                                                           FStarC_Tactics_Types.set_ps_psc
                                                             psc uu___22 in
                                                         FStarC_Effect.op_Colon_Equals
                                                           ps uu___21);
                                                        (let r1 =
                                                           interp_ctx name
                                                             (fun uu___21 ->
                                                                let uu___22 =
                                                                  t a11 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 in
                                                                uu___22 ps) in
                                                         let uu___21 =
                                                           let uu___22 =
                                                             FStarC_TypeChecker_Primops_Base.psc_range
                                                               psc in
                                                           embed er uu___22
                                                             r1 ncb in
                                                         FStar_Pervasives_Native.Some
                                                           uu___21)))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_10 (name : Prims.string)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::[] ->
      let uu___11 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___11
        (fun a12 ->
           let uu___12 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___12
             (fun a21 ->
                let uu___13 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___13
                  (fun a31 ->
                     let uu___14 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___14
                       (fun a41 ->
                          let uu___15 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___15
                            (fun a51 ->
                               let uu___16 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___16
                                 (fun a61 ->
                                    let uu___17 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___17
                                      (fun a71 ->
                                         let uu___18 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___18
                                           (fun a81 ->
                                              let uu___19 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___19
                                                (fun a91 ->
                                                   let uu___20 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___20
                                                     (fun a101 ->
                                                        let uu___21 =
                                                          unembed
                                                            FStarC_Tactics_Embedding.e_ref_proofstate
                                                            a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___21
                                                          (fun ps ->
                                                             (let uu___23 =
                                                                let uu___24 =
                                                                  FStarC_Effect.op_Bang
                                                                    ps in
                                                                FStarC_Tactics_Types.set_ps_psc
                                                                  psc uu___24 in
                                                              FStarC_Effect.op_Colon_Equals
                                                                ps uu___23);
                                                             (let r1 =
                                                                interp_ctx
                                                                  name
                                                                  (fun
                                                                    uu___23
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    t a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101 in
                                                                    uu___24
                                                                    ps) in
                                                              let uu___23 =
                                                                let uu___24 =
                                                                  FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                embed er
                                                                  uu___24 r1
                                                                  ncb in
                                                              FStar_Pervasives_Native.Some
                                                                uu___23))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_11 (name : Prims.string)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 -> 't9 -> 't10 -> 't11 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::[] ->
      let uu___12 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___12
        (fun a13 ->
           let uu___13 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___13
             (fun a21 ->
                let uu___14 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___14
                  (fun a31 ->
                     let uu___15 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___15
                       (fun a41 ->
                          let uu___16 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___16
                            (fun a51 ->
                               let uu___17 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___17
                                 (fun a61 ->
                                    let uu___18 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___18
                                      (fun a71 ->
                                         let uu___19 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___19
                                           (fun a81 ->
                                              let uu___20 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___20
                                                (fun a91 ->
                                                   let uu___21 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___21
                                                     (fun a101 ->
                                                        let uu___22 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___22
                                                          (fun a111 ->
                                                             let uu___23 =
                                                               unembed
                                                                 FStarC_Tactics_Embedding.e_ref_proofstate
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___23
                                                               (fun ps ->
                                                                  (let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___26 in
                                                                   FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___25);
                                                                  (let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    t a13 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 in
                                                                    uu___26
                                                                    ps) in
                                                                   let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___26
                                                                    r1 ncb in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu___25)))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_12 (name : Prims.string)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 ->
                    't9 ->
                      't10 -> 't11 -> 't12 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::[] ->
      let uu___13 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___13
        (fun a14 ->
           let uu___14 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___14
             (fun a21 ->
                let uu___15 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___15
                  (fun a31 ->
                     let uu___16 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___16
                       (fun a41 ->
                          let uu___17 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___17
                            (fun a51 ->
                               let uu___18 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___18
                                 (fun a61 ->
                                    let uu___19 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___19
                                      (fun a71 ->
                                         let uu___20 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___20
                                           (fun a81 ->
                                              let uu___21 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___21
                                                (fun a91 ->
                                                   let uu___22 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___22
                                                     (fun a101 ->
                                                        let uu___23 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___23
                                                          (fun a111 ->
                                                             let uu___24 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___24
                                                               (fun a121 ->
                                                                  let uu___25
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a13 ncb in
                                                                  FStarC_Option.bind
                                                                    uu___25
                                                                    (
                                                                    fun ps ->
                                                                    (
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___28 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___27);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    t a14 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121 in
                                                                    uu___28
                                                                    ps) in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___28
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___27))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_13 (name : Prims.string)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 ->
                    't9 ->
                      't10 ->
                        't11 -> 't12 -> 't13 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::[] ->
      let uu___14 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___14
        (fun a15 ->
           let uu___15 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___15
             (fun a21 ->
                let uu___16 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___16
                  (fun a31 ->
                     let uu___17 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___17
                       (fun a41 ->
                          let uu___18 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___18
                            (fun a51 ->
                               let uu___19 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___19
                                 (fun a61 ->
                                    let uu___20 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___20
                                      (fun a71 ->
                                         let uu___21 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___21
                                           (fun a81 ->
                                              let uu___22 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___22
                                                (fun a91 ->
                                                   let uu___23 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___23
                                                     (fun a101 ->
                                                        let uu___24 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___24
                                                          (fun a111 ->
                                                             let uu___25 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___25
                                                               (fun a121 ->
                                                                  let uu___26
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___26
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a14 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___27
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___30 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___29);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    t a15 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 in
                                                                    uu___30
                                                                    ps) in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___30
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___29)))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_14 (name : Prims.string)
  (t :
    't1 ->
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
                          't12 -> 't13 -> 't14 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::[] ->
      let uu___15 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___15
        (fun a16 ->
           let uu___16 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___16
             (fun a21 ->
                let uu___17 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___17
                  (fun a31 ->
                     let uu___18 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___18
                       (fun a41 ->
                          let uu___19 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___19
                            (fun a51 ->
                               let uu___20 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___20
                                 (fun a61 ->
                                    let uu___21 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___21
                                      (fun a71 ->
                                         let uu___22 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___22
                                           (fun a81 ->
                                              let uu___23 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___23
                                                (fun a91 ->
                                                   let uu___24 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___24
                                                     (fun a101 ->
                                                        let uu___25 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___25
                                                          (fun a111 ->
                                                             let uu___26 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___26
                                                               (fun a121 ->
                                                                  let uu___27
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___27
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a15 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___29
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___32 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___31);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    t a16 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141 in
                                                                    uu___32
                                                                    ps) in
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___32
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___31))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_15 (name : Prims.string)
  (t :
    't1 ->
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
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::[] ->
      let uu___16 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___16
        (fun a17 ->
           let uu___17 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___17
             (fun a21 ->
                let uu___18 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___18
                  (fun a31 ->
                     let uu___19 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___19
                       (fun a41 ->
                          let uu___20 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___20
                            (fun a51 ->
                               let uu___21 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___21
                                 (fun a61 ->
                                    let uu___22 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___22
                                      (fun a71 ->
                                         let uu___23 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___23
                                           (fun a81 ->
                                              let uu___24 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___24
                                                (fun a91 ->
                                                   let uu___25 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___25
                                                     (fun a101 ->
                                                        let uu___26 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___26
                                                          (fun a111 ->
                                                             let uu___27 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___27
                                                               (fun a121 ->
                                                                  let uu___28
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___28
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a16 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___34 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___33);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    t a17 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 in
                                                                    uu___34
                                                                    ps) in
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___34
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___33)))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_16 (name : Prims.string)
  (t :
    't1 ->
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
                                't15 -> 't16 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::[] ->
      let uu___17 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___17
        (fun a18 ->
           let uu___18 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___18
             (fun a21 ->
                let uu___19 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___19
                  (fun a31 ->
                     let uu___20 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___20
                       (fun a41 ->
                          let uu___21 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___21
                            (fun a51 ->
                               let uu___22 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___22
                                 (fun a61 ->
                                    let uu___23 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___23
                                      (fun a71 ->
                                         let uu___24 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___24
                                           (fun a81 ->
                                              let uu___25 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___25
                                                (fun a91 ->
                                                   let uu___26 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___26
                                                     (fun a101 ->
                                                        let uu___27 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___27
                                                          (fun a111 ->
                                                             let uu___28 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___28
                                                               (fun a121 ->
                                                                  let uu___29
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___29
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a17 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___36 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___35);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    t a18 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111 a121
                                                                    a131 a141
                                                                    a151 a161 in
                                                                    uu___36
                                                                    ps) in
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___36
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___35))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_17 (name : Prims.string)
  (t :
    't1 ->
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
                                  't16 -> 't17 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::[] ->
      let uu___18 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___18
        (fun a19 ->
           let uu___19 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___19
             (fun a21 ->
                let uu___20 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___20
                  (fun a31 ->
                     let uu___21 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___21
                       (fun a41 ->
                          let uu___22 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___22
                            (fun a51 ->
                               let uu___23 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___23
                                 (fun a61 ->
                                    let uu___24 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___24
                                      (fun a71 ->
                                         let uu___25 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___25
                                           (fun a81 ->
                                              let uu___26 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___26
                                                (fun a91 ->
                                                   let uu___27 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___27
                                                     (fun a101 ->
                                                        let uu___28 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___28
                                                          (fun a111 ->
                                                             let uu___29 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___29
                                                               (fun a121 ->
                                                                  let uu___30
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___30
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a18 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___38 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___37);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    let uu___38
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
                                                                    uu___38
                                                                    ps) in
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___38
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___37)))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_18 (name : Prims.string)
  (t :
    't1 ->
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
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (e18 : 't18 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::[] ->
      let uu___19 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___19
        (fun a110 ->
           let uu___20 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___20
             (fun a21 ->
                let uu___21 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___21
                  (fun a31 ->
                     let uu___22 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___22
                       (fun a41 ->
                          let uu___23 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___23
                            (fun a51 ->
                               let uu___24 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___24
                                 (fun a61 ->
                                    let uu___25 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___25
                                      (fun a71 ->
                                         let uu___26 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___26
                                           (fun a81 ->
                                              let uu___27 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___27
                                                (fun a91 ->
                                                   let uu___28 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___28
                                                     (fun a101 ->
                                                        let uu___29 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___29
                                                          (fun a111 ->
                                                             let uu___30 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___30
                                                               (fun a121 ->
                                                                  let uu___31
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___31
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a19 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___37
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___40 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___39);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    let uu___40
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
                                                                    uu___40
                                                                    ps) in
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___40
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___39))))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_19 (name : Prims.string)
  (t :
    't1 ->
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
                                        't19 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (e18 : 't18 FStarC_Syntax_Embeddings_Base.embedding)
  (e19 : 't19 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::(a20, uu___19)::[] ->
      let uu___20 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___20
        (fun a110 ->
           let uu___21 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___21
             (fun a21 ->
                let uu___22 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___22
                  (fun a31 ->
                     let uu___23 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___23
                       (fun a41 ->
                          let uu___24 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___24
                            (fun a51 ->
                               let uu___25 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___25
                                 (fun a61 ->
                                    let uu___26 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___26
                                      (fun a71 ->
                                         let uu___27 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___27
                                           (fun a81 ->
                                              let uu___28 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___28
                                                (fun a91 ->
                                                   let uu___29 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___29
                                                     (fun a101 ->
                                                        let uu___30 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___30
                                                          (fun a111 ->
                                                             let uu___31 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___31
                                                               (fun a121 ->
                                                                  let uu___32
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___32
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a20 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___39
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___42 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___41);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    let uu___42
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
                                                                    uu___42
                                                                    ps) in
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___42
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___41)))))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_interpretation_20 (name : Prims.string)
  (t :
    't1 ->
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
                                          't20 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (e18 : 't18 FStarC_Syntax_Embeddings_Base.embedding)
  (e19 : 't19 FStarC_Syntax_Embeddings_Base.embedding)
  (e20 : 't20 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::(a20, uu___19)::(a21, uu___20)::[] ->
      let uu___21 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___21
        (fun a110 ->
           let uu___22 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___22
             (fun a22 ->
                let uu___23 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___23
                  (fun a31 ->
                     let uu___24 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___24
                       (fun a41 ->
                          let uu___25 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___25
                            (fun a51 ->
                               let uu___26 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___26
                                 (fun a61 ->
                                    let uu___27 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___27
                                      (fun a71 ->
                                         let uu___28 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___28
                                           (fun a81 ->
                                              let uu___29 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___29
                                                (fun a91 ->
                                                   let uu___30 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___30
                                                     (fun a101 ->
                                                        let uu___31 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___31
                                                          (fun a111 ->
                                                             let uu___32 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___32
                                                               (fun a121 ->
                                                                  let uu___33
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___33
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a141
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a151
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a161
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___37
                                                                    (fun a171
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___38
                                                                    (fun a181
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___39
                                                                    (fun a191
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    unembed
                                                                    e20 a20
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___40
                                                                    (fun a201
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate
                                                                    a21 ncb in
                                                                    FStarC_Option.bind
                                                                    uu___41
                                                                    (fun ps
                                                                    ->
                                                                    (
                                                                    let uu___43
                                                                    =
                                                                    let uu___44
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    ps in
                                                                    FStarC_Tactics_Types.set_ps_psc
                                                                    psc
                                                                    uu___44 in
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    ps
                                                                    uu___43);
                                                                    (
                                                                    let r1 =
                                                                    interp_ctx
                                                                    name
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    let uu___44
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
                                                                    uu___44
                                                                    ps) in
                                                                    let uu___43
                                                                    =
                                                                    let uu___44
                                                                    =
                                                                    FStarC_TypeChecker_Primops_Base.psc_range
                                                                    psc in
                                                                    embed er
                                                                    uu___44
                                                                    r1 ncb in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___43))))))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_1 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t : 't1 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::[] ->
      let uu___2 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___2
        (fun a11 ->
           let uu___3 =
             FStarC_TypeChecker_NBETerm.unembed
               FStarC_Tactics_Embedding.e_ref_proofstate_nbe cb a2 in
           FStarC_Option.bind uu___3
             (fun ps ->
                let r1 =
                  interp_ctx name
                    (fun uu___4 -> let uu___5 = t a11 in uu___5 ps) in
                let uu___4 = FStarC_TypeChecker_NBETerm.embed er cb r1 in
                FStar_Pervasives_Native.Some uu___4))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_2 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t : 't1 -> 't2 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
      let uu___3 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___3
        (fun a11 ->
           let uu___4 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___4
             (fun a21 ->
                let uu___5 =
                  FStarC_TypeChecker_NBETerm.unembed
                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe cb a3 in
                FStarC_Option.bind uu___5
                  (fun ps ->
                     let r1 =
                       interp_ctx name
                         (fun uu___6 -> let uu___7 = t a11 a21 in uu___7 ps) in
                     let uu___6 = FStarC_TypeChecker_NBETerm.embed er cb r1 in
                     FStar_Pervasives_Native.Some uu___6)))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_3 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t : 't1 -> 't2 -> 't3 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::[] ->
      let uu___4 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___4
        (fun a11 ->
           let uu___5 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___5
             (fun a21 ->
                let uu___6 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___6
                  (fun a31 ->
                     let uu___7 =
                       FStarC_TypeChecker_NBETerm.unembed
                         FStarC_Tactics_Embedding.e_ref_proofstate_nbe cb a4 in
                     FStarC_Option.bind uu___7
                       (fun ps ->
                          let r1 =
                            interp_ctx name
                              (fun uu___8 ->
                                 let uu___9 = t a11 a21 a31 in uu___9 ps) in
                          let uu___8 =
                            FStarC_TypeChecker_NBETerm.embed er cb r1 in
                          FStar_Pervasives_Native.Some uu___8))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_4 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t : 't1 -> 't2 -> 't3 -> 't4 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::[]
      ->
      let uu___5 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___5
        (fun a11 ->
           let uu___6 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___6
             (fun a21 ->
                let uu___7 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___7
                  (fun a31 ->
                     let uu___8 = FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___8
                       (fun a41 ->
                          let uu___9 =
                            FStarC_TypeChecker_NBETerm.unembed
                              FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                              cb a5 in
                          FStarC_Option.bind uu___9
                            (fun ps ->
                               let r1 =
                                 interp_ctx name
                                   (fun uu___10 ->
                                      let uu___11 = t a11 a21 a31 a41 in
                                      uu___11 ps) in
                               let uu___10 =
                                 FStarC_TypeChecker_NBETerm.embed er cb r1 in
                               FStar_Pervasives_Native.Some uu___10)))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_5 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::[] ->
      let uu___6 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___6
        (fun a11 ->
           let uu___7 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___7
             (fun a21 ->
                let uu___8 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___8
                  (fun a31 ->
                     let uu___9 = FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___9
                       (fun a41 ->
                          let uu___10 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___10
                            (fun a51 ->
                               let uu___11 =
                                 FStarC_TypeChecker_NBETerm.unembed
                                   FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                   cb a6 in
                               FStarC_Option.bind uu___11
                                 (fun ps ->
                                    let r1 =
                                      interp_ctx name
                                        (fun uu___12 ->
                                           let uu___13 =
                                             t a11 a21 a31 a41 a51 in
                                           uu___13 ps) in
                                    let uu___12 =
                                      FStarC_TypeChecker_NBETerm.embed er cb
                                        r1 in
                                    FStar_Pervasives_Native.Some uu___12))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_6 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::[] ->
      let uu___7 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___7
        (fun a11 ->
           let uu___8 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___8
             (fun a21 ->
                let uu___9 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___9
                  (fun a31 ->
                     let uu___10 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___10
                       (fun a41 ->
                          let uu___11 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___11
                            (fun a51 ->
                               let uu___12 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___12
                                 (fun a61 ->
                                    let uu___13 =
                                      FStarC_TypeChecker_NBETerm.unembed
                                        FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                        cb a7 in
                                    FStarC_Option.bind uu___13
                                      (fun ps ->
                                         let r1 =
                                           interp_ctx name
                                             (fun uu___14 ->
                                                let uu___15 =
                                                  t a11 a21 a31 a41 a51 a61 in
                                                uu___15 ps) in
                                         let uu___14 =
                                           FStarC_TypeChecker_NBETerm.embed
                                             er cb r1 in
                                         FStar_Pervasives_Native.Some uu___14)))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_7 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
      't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::[] ->
      let uu___8 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___8
        (fun a11 ->
           let uu___9 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___9
             (fun a21 ->
                let uu___10 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___10
                  (fun a31 ->
                     let uu___11 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___11
                       (fun a41 ->
                          let uu___12 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___12
                            (fun a51 ->
                               let uu___13 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___13
                                 (fun a61 ->
                                    let uu___14 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___14
                                      (fun a71 ->
                                         let uu___15 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                             cb a8 in
                                         FStarC_Option.bind uu___15
                                           (fun ps ->
                                              let r1 =
                                                interp_ctx name
                                                  (fun uu___16 ->
                                                     let uu___17 =
                                                       t a11 a21 a31 a41 a51
                                                         a61 a71 in
                                                     uu___17 ps) in
                                              let uu___16 =
                                                FStarC_TypeChecker_NBETerm.embed
                                                  er cb r1 in
                                              FStar_Pervasives_Native.Some
                                                uu___16))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_8 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
      't2 ->
        't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::[] ->
      let uu___9 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___9
        (fun a11 ->
           let uu___10 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___10
             (fun a21 ->
                let uu___11 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___11
                  (fun a31 ->
                     let uu___12 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___12
                       (fun a41 ->
                          let uu___13 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___13
                            (fun a51 ->
                               let uu___14 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___14
                                 (fun a61 ->
                                    let uu___15 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___15
                                      (fun a71 ->
                                         let uu___16 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___16
                                           (fun a81 ->
                                              let uu___17 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                  cb a9 in
                                              FStarC_Option.bind uu___17
                                                (fun ps ->
                                                   let r1 =
                                                     interp_ctx name
                                                       (fun uu___18 ->
                                                          let uu___19 =
                                                            t a11 a21 a31 a41
                                                              a51 a61 a71 a81 in
                                                          uu___19 ps) in
                                                   let uu___18 =
                                                     FStarC_TypeChecker_NBETerm.embed
                                                       er cb r1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu___18)))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_9 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::[]
      ->
      let uu___10 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___10
        (fun a11 ->
           let uu___11 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___11
             (fun a21 ->
                let uu___12 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___12
                  (fun a31 ->
                     let uu___13 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___13
                       (fun a41 ->
                          let uu___14 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___14
                            (fun a51 ->
                               let uu___15 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___15
                                 (fun a61 ->
                                    let uu___16 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___16
                                      (fun a71 ->
                                         let uu___17 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___17
                                           (fun a81 ->
                                              let uu___18 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___18
                                                (fun a91 ->
                                                   let uu___19 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                       cb a10 in
                                                   FStarC_Option.bind uu___19
                                                     (fun ps ->
                                                        let r1 =
                                                          interp_ctx name
                                                            (fun uu___20 ->
                                                               let uu___21 =
                                                                 t a11 a21
                                                                   a31 a41
                                                                   a51 a61
                                                                   a71 a81
                                                                   a91 in
                                                               uu___21 ps) in
                                                        let uu___20 =
                                                          FStarC_TypeChecker_NBETerm.embed
                                                            er cb r1 in
                                                        FStar_Pervasives_Native.Some
                                                          uu___20))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_10 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::[] ->
      let uu___11 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___11
        (fun a12 ->
           let uu___12 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___12
             (fun a21 ->
                let uu___13 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___13
                  (fun a31 ->
                     let uu___14 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___14
                       (fun a41 ->
                          let uu___15 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___15
                            (fun a51 ->
                               let uu___16 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___16
                                 (fun a61 ->
                                    let uu___17 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___17
                                      (fun a71 ->
                                         let uu___18 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___18
                                           (fun a81 ->
                                              let uu___19 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___19
                                                (fun a91 ->
                                                   let uu___20 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___20
                                                     (fun a101 ->
                                                        let uu___21 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                            cb a11 in
                                                        FStarC_Option.bind
                                                          uu___21
                                                          (fun ps ->
                                                             let r1 =
                                                               interp_ctx
                                                                 name
                                                                 (fun uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    t a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101 in
                                                                    uu___23
                                                                    ps) in
                                                             let uu___22 =
                                                               FStarC_TypeChecker_NBETerm.embed
                                                                 er cb r1 in
                                                             FStar_Pervasives_Native.Some
                                                               uu___22)))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_11 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 -> 't9 -> 't10 -> 't11 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::[] ->
      let uu___12 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___12
        (fun a13 ->
           let uu___13 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___13
             (fun a21 ->
                let uu___14 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___14
                  (fun a31 ->
                     let uu___15 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___15
                       (fun a41 ->
                          let uu___16 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___16
                            (fun a51 ->
                               let uu___17 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___17
                                 (fun a61 ->
                                    let uu___18 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___18
                                      (fun a71 ->
                                         let uu___19 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___19
                                           (fun a81 ->
                                              let uu___20 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___20
                                                (fun a91 ->
                                                   let uu___21 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___21
                                                     (fun a101 ->
                                                        let uu___22 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___22
                                                          (fun a111 ->
                                                             let uu___23 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___23
                                                               (fun ps ->
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
                                                                    uu___25
                                                                    ps) in
                                                                  let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu___24))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_12 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 ->
                    't9 ->
                      't10 -> 't11 -> 't12 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::[] ->
      let uu___13 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___13
        (fun a14 ->
           let uu___14 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___14
             (fun a21 ->
                let uu___15 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___15
                  (fun a31 ->
                     let uu___16 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___16
                       (fun a41 ->
                          let uu___17 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___17
                            (fun a51 ->
                               let uu___18 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___18
                                 (fun a61 ->
                                    let uu___19 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___19
                                      (fun a71 ->
                                         let uu___20 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___20
                                           (fun a81 ->
                                              let uu___21 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___21
                                                (fun a91 ->
                                                   let uu___22 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___22
                                                     (fun a101 ->
                                                        let uu___23 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___23
                                                          (fun a111 ->
                                                             let uu___24 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___24
                                                               (fun a121 ->
                                                                  let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a13 in
                                                                  FStarC_Option.bind
                                                                    uu___25
                                                                    (
                                                                    fun ps ->
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
                                                                    uu___27
                                                                    ps) in
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___26)))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_13 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 ->
                    't9 ->
                      't10 ->
                        't11 -> 't12 -> 't13 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::[] ->
      let uu___14 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___14
        (fun a15 ->
           let uu___15 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___15
             (fun a21 ->
                let uu___16 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___16
                  (fun a31 ->
                     let uu___17 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___17
                       (fun a41 ->
                          let uu___18 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___18
                            (fun a51 ->
                               let uu___19 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___19
                                 (fun a61 ->
                                    let uu___20 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___20
                                      (fun a71 ->
                                         let uu___21 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___21
                                           (fun a81 ->
                                              let uu___22 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___22
                                                (fun a91 ->
                                                   let uu___23 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___23
                                                     (fun a101 ->
                                                        let uu___24 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___24
                                                          (fun a111 ->
                                                             let uu___25 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___25
                                                               (fun a121 ->
                                                                  let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___26
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a14 in
                                                                    FStarC_Option.bind
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
                                                                    uu___29
                                                                    ps) in
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___28))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_14 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
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
                          't12 -> 't13 -> 't14 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::[] ->
      let uu___15 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___15
        (fun a16 ->
           let uu___16 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___16
             (fun a21 ->
                let uu___17 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___17
                  (fun a31 ->
                     let uu___18 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___18
                       (fun a41 ->
                          let uu___19 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___19
                            (fun a51 ->
                               let uu___20 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___20
                                 (fun a61 ->
                                    let uu___21 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___21
                                      (fun a71 ->
                                         let uu___22 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___22
                                           (fun a81 ->
                                              let uu___23 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___23
                                                (fun a91 ->
                                                   let uu___24 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___24
                                                     (fun a101 ->
                                                        let uu___25 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___25
                                                          (fun a111 ->
                                                             let uu___26 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___26
                                                               (fun a121 ->
                                                                  let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___27
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a15 in
                                                                    FStarC_Option.bind
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
                                                                    uu___31
                                                                    ps) in
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___30)))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_15 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
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
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::[] ->
      let uu___16 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___16
        (fun a17 ->
           let uu___17 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___17
             (fun a21 ->
                let uu___18 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___18
                  (fun a31 ->
                     let uu___19 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___19
                       (fun a41 ->
                          let uu___20 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___20
                            (fun a51 ->
                               let uu___21 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___21
                                 (fun a61 ->
                                    let uu___22 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___22
                                      (fun a71 ->
                                         let uu___23 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___23
                                           (fun a81 ->
                                              let uu___24 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___24
                                                (fun a91 ->
                                                   let uu___25 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___25
                                                     (fun a101 ->
                                                        let uu___26 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___26
                                                          (fun a111 ->
                                                             let uu___27 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___27
                                                               (fun a121 ->
                                                                  let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___28
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a16 in
                                                                    FStarC_Option.bind
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
                                                                    uu___33
                                                                    ps) in
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___32))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_16 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
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
                                't15 -> 't16 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::[] ->
      let uu___17 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___17
        (fun a18 ->
           let uu___18 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___18
             (fun a21 ->
                let uu___19 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___19
                  (fun a31 ->
                     let uu___20 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___20
                       (fun a41 ->
                          let uu___21 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___21
                            (fun a51 ->
                               let uu___22 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___22
                                 (fun a61 ->
                                    let uu___23 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___23
                                      (fun a71 ->
                                         let uu___24 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___24
                                           (fun a81 ->
                                              let uu___25 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___25
                                                (fun a91 ->
                                                   let uu___26 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___26
                                                     (fun a101 ->
                                                        let uu___27 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___27
                                                          (fun a111 ->
                                                             let uu___28 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___28
                                                               (fun a121 ->
                                                                  let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___29
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a17 in
                                                                    FStarC_Option.bind
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
                                                                    uu___35
                                                                    ps) in
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___34)))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_17 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
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
                                  't16 -> 't17 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::[] ->
      let uu___18 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___18
        (fun a19 ->
           let uu___19 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___19
             (fun a21 ->
                let uu___20 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___20
                  (fun a31 ->
                     let uu___21 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___21
                       (fun a41 ->
                          let uu___22 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___22
                            (fun a51 ->
                               let uu___23 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___23
                                 (fun a61 ->
                                    let uu___24 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___24
                                      (fun a71 ->
                                         let uu___25 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___25
                                           (fun a81 ->
                                              let uu___26 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___26
                                                (fun a91 ->
                                                   let uu___27 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___27
                                                     (fun a101 ->
                                                        let uu___28 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___28
                                                          (fun a111 ->
                                                             let uu___29 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___29
                                                               (fun a121 ->
                                                                  let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___30
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a18 in
                                                                    FStarC_Option.bind
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
                                                                    uu___37
                                                                    ps) in
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___36))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_18 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
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
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (e18 : 't18 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::[] ->
      let uu___19 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___19
        (fun a110 ->
           let uu___20 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___20
             (fun a21 ->
                let uu___21 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___21
                  (fun a31 ->
                     let uu___22 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___22
                       (fun a41 ->
                          let uu___23 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___23
                            (fun a51 ->
                               let uu___24 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___24
                                 (fun a61 ->
                                    let uu___25 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___25
                                      (fun a71 ->
                                         let uu___26 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___26
                                           (fun a81 ->
                                              let uu___27 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___27
                                                (fun a91 ->
                                                   let uu___28 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___28
                                                     (fun a101 ->
                                                        let uu___29 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___29
                                                          (fun a111 ->
                                                             let uu___30 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___30
                                                               (fun a121 ->
                                                                  let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___31
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a19 in
                                                                    FStarC_Option.bind
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
                                                                    uu___39
                                                                    ps) in
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___38)))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_19 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
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
                                        't19 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (e18 : 't18 FStarC_TypeChecker_NBETerm.embedding)
  (e19 : 't19 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::(a20, uu___19)::[] ->
      let uu___20 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___20
        (fun a110 ->
           let uu___21 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___21
             (fun a21 ->
                let uu___22 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___22
                  (fun a31 ->
                     let uu___23 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___23
                       (fun a41 ->
                          let uu___24 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___24
                            (fun a51 ->
                               let uu___25 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___25
                                 (fun a61 ->
                                    let uu___26 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___26
                                      (fun a71 ->
                                         let uu___27 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___27
                                           (fun a81 ->
                                              let uu___28 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___28
                                                (fun a91 ->
                                                   let uu___29 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___29
                                                     (fun a101 ->
                                                        let uu___30 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___30
                                                          (fun a111 ->
                                                             let uu___31 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___31
                                                               (fun a121 ->
                                                                  let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___32
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Option.bind
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Option.bind
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a20 in
                                                                    FStarC_Option.bind
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
                                                                    uu___41
                                                                    ps) in
                                                                    let uu___40
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___40))))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_tactic_nbe_interpretation_20 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (t :
    't1 ->
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
                                          't20 -> 'r FStarC_Tactics_Monad.tac)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (e18 : 't18 FStarC_TypeChecker_NBETerm.embedding)
  (e19 : 't19 FStarC_TypeChecker_NBETerm.embedding)
  (e20 : 't20 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::(a20, uu___19)::(a21, uu___20)::[] ->
      let uu___21 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___21
        (fun a110 ->
           let uu___22 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___22
             (fun a22 ->
                let uu___23 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___23
                  (fun a31 ->
                     let uu___24 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___24
                       (fun a41 ->
                          let uu___25 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___25
                            (fun a51 ->
                               let uu___26 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___26
                                 (fun a61 ->
                                    let uu___27 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___27
                                      (fun a71 ->
                                         let uu___28 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___28
                                           (fun a81 ->
                                              let uu___29 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___29
                                                (fun a91 ->
                                                   let uu___30 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___30
                                                     (fun a101 ->
                                                        let uu___31 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___31
                                                          (fun a111 ->
                                                             let uu___32 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___32
                                                               (fun a121 ->
                                                                  let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___33
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a141
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a151
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a161
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
                                                                    uu___37
                                                                    (fun a171
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Option.bind
                                                                    uu___38
                                                                    (fun a181
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Option.bind
                                                                    uu___39
                                                                    (fun a191
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e20 cb
                                                                    a20 in
                                                                    FStarC_Option.bind
                                                                    uu___40
                                                                    (fun a201
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    FStarC_Tactics_Embedding.e_ref_proofstate_nbe
                                                                    cb a21 in
                                                                    FStarC_Option.bind
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
                                                                    uu___43
                                                                    ps) in
                                                                    let uu___42
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    er cb r1 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___42)))))))))))))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_1 (name : Prims.string) (f : 't1 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::[] ->
      let uu___1 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___1
        (fun a11 ->
           let r1 = interp_ctx name (fun uu___2 -> f a11) in
           let uu___2 =
             let uu___3 = FStarC_TypeChecker_Primops_Base.psc_range psc in
             embed er uu___3 r1 ncb in
           FStar_Pervasives_Native.Some uu___2)
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_2 (name : Prims.string) (f : 't1 -> 't2 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::[] ->
      let uu___2 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___2
        (fun a11 ->
           let uu___3 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___3
             (fun a21 ->
                let r1 = interp_ctx name (fun uu___4 -> f a11 a21) in
                let uu___4 =
                  let uu___5 = FStarC_TypeChecker_Primops_Base.psc_range psc in
                  embed er uu___5 r1 ncb in
                FStar_Pervasives_Native.Some uu___4))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_3 (name : Prims.string)
  (f : 't1 -> 't2 -> 't3 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
      let uu___3 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___3
        (fun a11 ->
           let uu___4 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___4
             (fun a21 ->
                let uu___5 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___5
                  (fun a31 ->
                     let r1 = interp_ctx name (fun uu___6 -> f a11 a21 a31) in
                     let uu___6 =
                       let uu___7 =
                         FStarC_TypeChecker_Primops_Base.psc_range psc in
                       embed er uu___7 r1 ncb in
                     FStar_Pervasives_Native.Some uu___6)))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_4 (name : Prims.string)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::[] ->
      let uu___4 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___4
        (fun a11 ->
           let uu___5 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___5
             (fun a21 ->
                let uu___6 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___6
                  (fun a31 ->
                     let uu___7 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___7
                       (fun a41 ->
                          let r1 =
                            interp_ctx name (fun uu___8 -> f a11 a21 a31 a41) in
                          let uu___8 =
                            let uu___9 =
                              FStarC_TypeChecker_Primops_Base.psc_range psc in
                            embed er uu___9 r1 ncb in
                          FStar_Pervasives_Native.Some uu___8))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_5 (name : Prims.string)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::[]
      ->
      let uu___5 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___5
        (fun a11 ->
           let uu___6 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___6
             (fun a21 ->
                let uu___7 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___7
                  (fun a31 ->
                     let uu___8 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___8
                       (fun a41 ->
                          let uu___9 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___9
                            (fun a51 ->
                               let r1 =
                                 interp_ctx name
                                   (fun uu___10 -> f a11 a21 a31 a41 a51) in
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_TypeChecker_Primops_Base.psc_range
                                     psc in
                                 embed er uu___11 r1 ncb in
                               FStar_Pervasives_Native.Some uu___10)))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_6 (name : Prims.string)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::[] ->
      let uu___6 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___6
        (fun a11 ->
           let uu___7 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___7
             (fun a21 ->
                let uu___8 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___8
                  (fun a31 ->
                     let uu___9 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___9
                       (fun a41 ->
                          let uu___10 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___10
                            (fun a51 ->
                               let uu___11 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___11
                                 (fun a61 ->
                                    let r1 =
                                      interp_ctx name
                                        (fun uu___12 ->
                                           f a11 a21 a31 a41 a51 a61) in
                                    let uu___12 =
                                      let uu___13 =
                                        FStarC_TypeChecker_Primops_Base.psc_range
                                          psc in
                                      embed er uu___13 r1 ncb in
                                    FStar_Pervasives_Native.Some uu___12))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_7 (name : Prims.string)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::[] ->
      let uu___7 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___7
        (fun a11 ->
           let uu___8 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___8
             (fun a21 ->
                let uu___9 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___9
                  (fun a31 ->
                     let uu___10 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___10
                       (fun a41 ->
                          let uu___11 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___11
                            (fun a51 ->
                               let uu___12 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___12
                                 (fun a61 ->
                                    let uu___13 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___13
                                      (fun a71 ->
                                         let r1 =
                                           interp_ctx name
                                             (fun uu___14 ->
                                                f a11 a21 a31 a41 a51 a61 a71) in
                                         let uu___14 =
                                           let uu___15 =
                                             FStarC_TypeChecker_Primops_Base.psc_range
                                               psc in
                                           embed er uu___15 r1 ncb in
                                         FStar_Pervasives_Native.Some uu___14)))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_8 (name : Prims.string)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::[] ->
      let uu___8 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___8
        (fun a11 ->
           let uu___9 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___9
             (fun a21 ->
                let uu___10 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___10
                  (fun a31 ->
                     let uu___11 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___11
                       (fun a41 ->
                          let uu___12 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___12
                            (fun a51 ->
                               let uu___13 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___13
                                 (fun a61 ->
                                    let uu___14 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___14
                                      (fun a71 ->
                                         let uu___15 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___15
                                           (fun a81 ->
                                              let r1 =
                                                interp_ctx name
                                                  (fun uu___16 ->
                                                     f a11 a21 a31 a41 a51
                                                       a61 a71 a81) in
                                              let uu___16 =
                                                let uu___17 =
                                                  FStarC_TypeChecker_Primops_Base.psc_range
                                                    psc in
                                                embed er uu___17 r1 ncb in
                                              FStar_Pervasives_Native.Some
                                                uu___16))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_9 (name : Prims.string)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::[] ->
      let uu___9 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___9
        (fun a11 ->
           let uu___10 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___10
             (fun a21 ->
                let uu___11 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___11
                  (fun a31 ->
                     let uu___12 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___12
                       (fun a41 ->
                          let uu___13 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___13
                            (fun a51 ->
                               let uu___14 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___14
                                 (fun a61 ->
                                    let uu___15 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___15
                                      (fun a71 ->
                                         let uu___16 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___16
                                           (fun a81 ->
                                              let uu___17 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___17
                                                (fun a91 ->
                                                   let r1 =
                                                     interp_ctx name
                                                       (fun uu___18 ->
                                                          f a11 a21 a31 a41
                                                            a51 a61 a71 a81
                                                            a91) in
                                                   let uu___18 =
                                                     let uu___19 =
                                                       FStarC_TypeChecker_Primops_Base.psc_range
                                                         psc in
                                                     embed er uu___19 r1 ncb in
                                                   FStar_Pervasives_Native.Some
                                                     uu___18)))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_10 (name : Prims.string)
  (f :
    't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::[]
      ->
      let uu___10 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___10
        (fun a11 ->
           let uu___11 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___11
             (fun a21 ->
                let uu___12 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___12
                  (fun a31 ->
                     let uu___13 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___13
                       (fun a41 ->
                          let uu___14 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___14
                            (fun a51 ->
                               let uu___15 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___15
                                 (fun a61 ->
                                    let uu___16 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___16
                                      (fun a71 ->
                                         let uu___17 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___17
                                           (fun a81 ->
                                              let uu___18 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___18
                                                (fun a91 ->
                                                   let uu___19 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___19
                                                     (fun a101 ->
                                                        let r1 =
                                                          interp_ctx name
                                                            (fun uu___20 ->
                                                               f a11 a21 a31
                                                                 a41 a51 a61
                                                                 a71 a81 a91
                                                                 a101) in
                                                        let uu___20 =
                                                          let uu___21 =
                                                            FStarC_TypeChecker_Primops_Base.psc_range
                                                              psc in
                                                          embed er uu___21 r1
                                                            ncb in
                                                        FStar_Pervasives_Native.Some
                                                          uu___20))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_11 (name : Prims.string)
  (f :
    't1 ->
      't2 ->
        't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::[] ->
      let uu___11 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___11
        (fun a12 ->
           let uu___12 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___12
             (fun a21 ->
                let uu___13 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___13
                  (fun a31 ->
                     let uu___14 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___14
                       (fun a41 ->
                          let uu___15 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___15
                            (fun a51 ->
                               let uu___16 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___16
                                 (fun a61 ->
                                    let uu___17 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___17
                                      (fun a71 ->
                                         let uu___18 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___18
                                           (fun a81 ->
                                              let uu___19 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___19
                                                (fun a91 ->
                                                   let uu___20 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___20
                                                     (fun a101 ->
                                                        let uu___21 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___21
                                                          (fun a111 ->
                                                             let r1 =
                                                               interp_ctx
                                                                 name
                                                                 (fun uu___22
                                                                    ->
                                                                    f a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111) in
                                                             let uu___22 =
                                                               let uu___23 =
                                                                 FStarC_TypeChecker_Primops_Base.psc_range
                                                                   psc in
                                                               embed er
                                                                 uu___23 r1
                                                                 ncb in
                                                             FStar_Pervasives_Native.Some
                                                               uu___22)))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_12 (name : Prims.string)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::[] ->
      let uu___12 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___12
        (fun a13 ->
           let uu___13 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___13
             (fun a21 ->
                let uu___14 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___14
                  (fun a31 ->
                     let uu___15 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___15
                       (fun a41 ->
                          let uu___16 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___16
                            (fun a51 ->
                               let uu___17 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___17
                                 (fun a61 ->
                                    let uu___18 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___18
                                      (fun a71 ->
                                         let uu___19 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___19
                                           (fun a81 ->
                                              let uu___20 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___20
                                                (fun a91 ->
                                                   let uu___21 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___21
                                                     (fun a101 ->
                                                        let uu___22 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___22
                                                          (fun a111 ->
                                                             let uu___23 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___23
                                                               (fun a121 ->
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_13 (name : Prims.string)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::[] ->
      let uu___13 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___13
        (fun a14 ->
           let uu___14 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___14
             (fun a21 ->
                let uu___15 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___15
                  (fun a31 ->
                     let uu___16 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___16
                       (fun a41 ->
                          let uu___17 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___17
                            (fun a51 ->
                               let uu___18 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___18
                                 (fun a61 ->
                                    let uu___19 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___19
                                      (fun a71 ->
                                         let uu___20 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___20
                                           (fun a81 ->
                                              let uu___21 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___21
                                                (fun a91 ->
                                                   let uu___22 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___22
                                                     (fun a101 ->
                                                        let uu___23 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___23
                                                          (fun a111 ->
                                                             let uu___24 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___24
                                                               (fun a121 ->
                                                                  let uu___25
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___25
                                                                    (
                                                                    fun a131
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_14 (name : Prims.string)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::[] ->
      let uu___14 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___14
        (fun a15 ->
           let uu___15 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___15
             (fun a21 ->
                let uu___16 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___16
                  (fun a31 ->
                     let uu___17 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___17
                       (fun a41 ->
                          let uu___18 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___18
                            (fun a51 ->
                               let uu___19 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___19
                                 (fun a61 ->
                                    let uu___20 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___20
                                      (fun a71 ->
                                         let uu___21 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___21
                                           (fun a81 ->
                                              let uu___22 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___22
                                                (fun a91 ->
                                                   let uu___23 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___23
                                                     (fun a101 ->
                                                        let uu___24 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___24
                                                          (fun a111 ->
                                                             let uu___25 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___25
                                                               (fun a121 ->
                                                                  let uu___26
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___26
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_15 (name : Prims.string)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 ->
                    't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 't15 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::[] ->
      let uu___15 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___15
        (fun a16 ->
           let uu___16 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___16
             (fun a21 ->
                let uu___17 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___17
                  (fun a31 ->
                     let uu___18 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___18
                       (fun a41 ->
                          let uu___19 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___19
                            (fun a51 ->
                               let uu___20 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___20
                                 (fun a61 ->
                                    let uu___21 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___21
                                      (fun a71 ->
                                         let uu___22 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___22
                                           (fun a81 ->
                                              let uu___23 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___23
                                                (fun a91 ->
                                                   let uu___24 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___24
                                                     (fun a101 ->
                                                        let uu___25 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___25
                                                          (fun a111 ->
                                                             let uu___26 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___26
                                                               (fun a121 ->
                                                                  let uu___27
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___27
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_16 (name : Prims.string)
  (f :
    't1 ->
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
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::[] ->
      let uu___16 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___16
        (fun a17 ->
           let uu___17 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___17
             (fun a21 ->
                let uu___18 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___18
                  (fun a31 ->
                     let uu___19 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___19
                       (fun a41 ->
                          let uu___20 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___20
                            (fun a51 ->
                               let uu___21 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___21
                                 (fun a61 ->
                                    let uu___22 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___22
                                      (fun a71 ->
                                         let uu___23 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___23
                                           (fun a81 ->
                                              let uu___24 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___24
                                                (fun a91 ->
                                                   let uu___25 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___25
                                                     (fun a101 ->
                                                        let uu___26 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___26
                                                          (fun a111 ->
                                                             let uu___27 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___27
                                                               (fun a121 ->
                                                                  let uu___28
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___28
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_17 (name : Prims.string)
  (f :
    't1 ->
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
                          't12 -> 't13 -> 't14 -> 't15 -> 't16 -> 't17 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::[] ->
      let uu___17 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___17
        (fun a18 ->
           let uu___18 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___18
             (fun a21 ->
                let uu___19 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___19
                  (fun a31 ->
                     let uu___20 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___20
                       (fun a41 ->
                          let uu___21 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___21
                            (fun a51 ->
                               let uu___22 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___22
                                 (fun a61 ->
                                    let uu___23 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___23
                                      (fun a71 ->
                                         let uu___24 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___24
                                           (fun a81 ->
                                              let uu___25 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___25
                                                (fun a91 ->
                                                   let uu___26 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___26
                                                     (fun a101 ->
                                                        let uu___27 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___27
                                                          (fun a111 ->
                                                             let uu___28 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___28
                                                               (fun a121 ->
                                                                  let uu___29
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___29
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_18 (name : Prims.string)
  (f :
    't1 ->
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
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (e18 : 't18 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::[] ->
      let uu___18 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___18
        (fun a19 ->
           let uu___19 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___19
             (fun a21 ->
                let uu___20 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___20
                  (fun a31 ->
                     let uu___21 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___21
                       (fun a41 ->
                          let uu___22 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___22
                            (fun a51 ->
                               let uu___23 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___23
                                 (fun a61 ->
                                    let uu___24 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___24
                                      (fun a71 ->
                                         let uu___25 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___25
                                           (fun a81 ->
                                              let uu___26 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___26
                                                (fun a91 ->
                                                   let uu___27 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___27
                                                     (fun a101 ->
                                                        let uu___28 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___28
                                                          (fun a111 ->
                                                             let uu___29 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___29
                                                               (fun a121 ->
                                                                  let uu___30
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___30
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_19 (name : Prims.string)
  (f :
    't1 ->
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
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (e18 : 't18 FStarC_Syntax_Embeddings_Base.embedding)
  (e19 : 't19 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::[] ->
      let uu___19 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___19
        (fun a110 ->
           let uu___20 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___20
             (fun a21 ->
                let uu___21 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___21
                  (fun a31 ->
                     let uu___22 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___22
                       (fun a41 ->
                          let uu___23 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___23
                            (fun a51 ->
                               let uu___24 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___24
                                 (fun a61 ->
                                    let uu___25 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___25
                                      (fun a71 ->
                                         let uu___26 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___26
                                           (fun a81 ->
                                              let uu___27 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___27
                                                (fun a91 ->
                                                   let uu___28 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___28
                                                     (fun a101 ->
                                                        let uu___29 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___29
                                                          (fun a111 ->
                                                             let uu___30 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___30
                                                               (fun a121 ->
                                                                  let uu___31
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___31
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_interpretation_20 (name : Prims.string)
  (f :
    't1 ->
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
                                  't16 -> 't17 -> 't18 -> 't19 -> 't20 -> 'r)
  (e1 : 't1 FStarC_Syntax_Embeddings_Base.embedding)
  (e2 : 't2 FStarC_Syntax_Embeddings_Base.embedding)
  (e3 : 't3 FStarC_Syntax_Embeddings_Base.embedding)
  (e4 : 't4 FStarC_Syntax_Embeddings_Base.embedding)
  (e5 : 't5 FStarC_Syntax_Embeddings_Base.embedding)
  (e6 : 't6 FStarC_Syntax_Embeddings_Base.embedding)
  (e7 : 't7 FStarC_Syntax_Embeddings_Base.embedding)
  (e8 : 't8 FStarC_Syntax_Embeddings_Base.embedding)
  (e9 : 't9 FStarC_Syntax_Embeddings_Base.embedding)
  (e10 : 't10 FStarC_Syntax_Embeddings_Base.embedding)
  (e11 : 't11 FStarC_Syntax_Embeddings_Base.embedding)
  (e12 : 't12 FStarC_Syntax_Embeddings_Base.embedding)
  (e13 : 't13 FStarC_Syntax_Embeddings_Base.embedding)
  (e14 : 't14 FStarC_Syntax_Embeddings_Base.embedding)
  (e15 : 't15 FStarC_Syntax_Embeddings_Base.embedding)
  (e16 : 't16 FStarC_Syntax_Embeddings_Base.embedding)
  (e17 : 't17 FStarC_Syntax_Embeddings_Base.embedding)
  (e18 : 't18 FStarC_Syntax_Embeddings_Base.embedding)
  (e19 : 't19 FStarC_Syntax_Embeddings_Base.embedding)
  (e20 : 't20 FStarC_Syntax_Embeddings_Base.embedding)
  (er : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ncb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::(a20, uu___19)::[] ->
      let uu___20 = unembed e1 a1 ncb in
      FStarC_Option.bind uu___20
        (fun a110 ->
           let uu___21 = unembed e2 a2 ncb in
           FStarC_Option.bind uu___21
             (fun a21 ->
                let uu___22 = unembed e3 a3 ncb in
                FStarC_Option.bind uu___22
                  (fun a31 ->
                     let uu___23 = unembed e4 a4 ncb in
                     FStarC_Option.bind uu___23
                       (fun a41 ->
                          let uu___24 = unembed e5 a5 ncb in
                          FStarC_Option.bind uu___24
                            (fun a51 ->
                               let uu___25 = unembed e6 a6 ncb in
                               FStarC_Option.bind uu___25
                                 (fun a61 ->
                                    let uu___26 = unembed e7 a7 ncb in
                                    FStarC_Option.bind uu___26
                                      (fun a71 ->
                                         let uu___27 = unembed e8 a8 ncb in
                                         FStarC_Option.bind uu___27
                                           (fun a81 ->
                                              let uu___28 = unembed e9 a9 ncb in
                                              FStarC_Option.bind uu___28
                                                (fun a91 ->
                                                   let uu___29 =
                                                     unembed e10 a10 ncb in
                                                   FStarC_Option.bind uu___29
                                                     (fun a101 ->
                                                        let uu___30 =
                                                          unembed e11 a11 ncb in
                                                        FStarC_Option.bind
                                                          uu___30
                                                          (fun a111 ->
                                                             let uu___31 =
                                                               unembed e12
                                                                 a12 ncb in
                                                             FStarC_Option.bind
                                                               uu___31
                                                               (fun a121 ->
                                                                  let uu___32
                                                                    =
                                                                    unembed
                                                                    e13 a13
                                                                    ncb in
                                                                  FStarC_Option.bind
                                                                    uu___32
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    unembed
                                                                    e14 a14
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    unembed
                                                                    e15 a15
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    unembed
                                                                    e16 a16
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    unembed
                                                                    e17 a17
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    unembed
                                                                    e18 a18
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    unembed
                                                                    e19 a19
                                                                    ncb in
                                                                    FStarC_Option.bind
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    unembed
                                                                    e20 a20
                                                                    ncb in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_1 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs) (f : 't1 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::[] ->
      let uu___1 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___1
        (fun a11 ->
           let r1 = interp_ctx name (fun uu___2 -> f a11) in
           let uu___2 = FStarC_TypeChecker_NBETerm.embed er cb r1 in
           FStar_Pervasives_Native.Some uu___2)
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_2 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs) (f : 't1 -> 't2 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::[] ->
      let uu___2 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___2
        (fun a11 ->
           let uu___3 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___3
             (fun a21 ->
                let r1 = interp_ctx name (fun uu___4 -> f a11 a21) in
                let uu___4 = FStarC_TypeChecker_NBETerm.embed er cb r1 in
                FStar_Pervasives_Native.Some uu___4))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_3 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs) (f : 't1 -> 't2 -> 't3 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::[] ->
      let uu___3 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___3
        (fun a11 ->
           let uu___4 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___4
             (fun a21 ->
                let uu___5 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___5
                  (fun a31 ->
                     let r1 = interp_ctx name (fun uu___6 -> f a11 a21 a31) in
                     let uu___6 = FStarC_TypeChecker_NBETerm.embed er cb r1 in
                     FStar_Pervasives_Native.Some uu___6)))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_4 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::[] ->
      let uu___4 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___4
        (fun a11 ->
           let uu___5 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___5
             (fun a21 ->
                let uu___6 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___6
                  (fun a31 ->
                     let uu___7 = FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___7
                       (fun a41 ->
                          let r1 =
                            interp_ctx name (fun uu___8 -> f a11 a21 a31 a41) in
                          let uu___8 =
                            FStarC_TypeChecker_NBETerm.embed er cb r1 in
                          FStar_Pervasives_Native.Some uu___8))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_5 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::[]
      ->
      let uu___5 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___5
        (fun a11 ->
           let uu___6 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___6
             (fun a21 ->
                let uu___7 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___7
                  (fun a31 ->
                     let uu___8 = FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___8
                       (fun a41 ->
                          let uu___9 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___9
                            (fun a51 ->
                               let r1 =
                                 interp_ctx name
                                   (fun uu___10 -> f a11 a21 a31 a41 a51) in
                               let uu___10 =
                                 FStarC_TypeChecker_NBETerm.embed er cb r1 in
                               FStar_Pervasives_Native.Some uu___10)))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_6 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::[] ->
      let uu___6 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___6
        (fun a11 ->
           let uu___7 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___7
             (fun a21 ->
                let uu___8 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___8
                  (fun a31 ->
                     let uu___9 = FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___9
                       (fun a41 ->
                          let uu___10 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___10
                            (fun a51 ->
                               let uu___11 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___11
                                 (fun a61 ->
                                    let r1 =
                                      interp_ctx name
                                        (fun uu___12 ->
                                           f a11 a21 a31 a41 a51 a61) in
                                    let uu___12 =
                                      FStarC_TypeChecker_NBETerm.embed er cb
                                        r1 in
                                    FStar_Pervasives_Native.Some uu___12))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_7 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::[] ->
      let uu___7 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___7
        (fun a11 ->
           let uu___8 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___8
             (fun a21 ->
                let uu___9 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___9
                  (fun a31 ->
                     let uu___10 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___10
                       (fun a41 ->
                          let uu___11 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___11
                            (fun a51 ->
                               let uu___12 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___12
                                 (fun a61 ->
                                    let uu___13 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___13
                                      (fun a71 ->
                                         let r1 =
                                           interp_ctx name
                                             (fun uu___14 ->
                                                f a11 a21 a31 a41 a51 a61 a71) in
                                         let uu___14 =
                                           FStarC_TypeChecker_NBETerm.embed
                                             er cb r1 in
                                         FStar_Pervasives_Native.Some uu___14)))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_8 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::[] ->
      let uu___8 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___8
        (fun a11 ->
           let uu___9 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___9
             (fun a21 ->
                let uu___10 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___10
                  (fun a31 ->
                     let uu___11 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___11
                       (fun a41 ->
                          let uu___12 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___12
                            (fun a51 ->
                               let uu___13 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___13
                                 (fun a61 ->
                                    let uu___14 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___14
                                      (fun a71 ->
                                         let uu___15 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___15
                                           (fun a81 ->
                                              let r1 =
                                                interp_ctx name
                                                  (fun uu___16 ->
                                                     f a11 a21 a31 a41 a51
                                                       a61 a71 a81) in
                                              let uu___16 =
                                                FStarC_TypeChecker_NBETerm.embed
                                                  er cb r1 in
                                              FStar_Pervasives_Native.Some
                                                uu___16))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_9 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f : 't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::[] ->
      let uu___9 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___9
        (fun a11 ->
           let uu___10 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___10
             (fun a21 ->
                let uu___11 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___11
                  (fun a31 ->
                     let uu___12 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___12
                       (fun a41 ->
                          let uu___13 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___13
                            (fun a51 ->
                               let uu___14 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___14
                                 (fun a61 ->
                                    let uu___15 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___15
                                      (fun a71 ->
                                         let uu___16 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___16
                                           (fun a81 ->
                                              let uu___17 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___17
                                                (fun a91 ->
                                                   let r1 =
                                                     interp_ctx name
                                                       (fun uu___18 ->
                                                          f a11 a21 a31 a41
                                                            a51 a61 a71 a81
                                                            a91) in
                                                   let uu___18 =
                                                     FStarC_TypeChecker_NBETerm.embed
                                                       er cb r1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu___18)))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_10 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::[]
      ->
      let uu___10 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___10
        (fun a11 ->
           let uu___11 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___11
             (fun a21 ->
                let uu___12 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___12
                  (fun a31 ->
                     let uu___13 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___13
                       (fun a41 ->
                          let uu___14 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___14
                            (fun a51 ->
                               let uu___15 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___15
                                 (fun a61 ->
                                    let uu___16 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___16
                                      (fun a71 ->
                                         let uu___17 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___17
                                           (fun a81 ->
                                              let uu___18 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___18
                                                (fun a91 ->
                                                   let uu___19 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___19
                                                     (fun a101 ->
                                                        let r1 =
                                                          interp_ctx name
                                                            (fun uu___20 ->
                                                               f a11 a21 a31
                                                                 a41 a51 a61
                                                                 a71 a81 a91
                                                                 a101) in
                                                        let uu___20 =
                                                          FStarC_TypeChecker_NBETerm.embed
                                                            er cb r1 in
                                                        FStar_Pervasives_Native.Some
                                                          uu___20))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_11 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
      't2 ->
        't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::[] ->
      let uu___11 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___11
        (fun a12 ->
           let uu___12 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___12
             (fun a21 ->
                let uu___13 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___13
                  (fun a31 ->
                     let uu___14 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___14
                       (fun a41 ->
                          let uu___15 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___15
                            (fun a51 ->
                               let uu___16 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___16
                                 (fun a61 ->
                                    let uu___17 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___17
                                      (fun a71 ->
                                         let uu___18 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___18
                                           (fun a81 ->
                                              let uu___19 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___19
                                                (fun a91 ->
                                                   let uu___20 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___20
                                                     (fun a101 ->
                                                        let uu___21 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___21
                                                          (fun a111 ->
                                                             let r1 =
                                                               interp_ctx
                                                                 name
                                                                 (fun uu___22
                                                                    ->
                                                                    f a12 a21
                                                                    a31 a41
                                                                    a51 a61
                                                                    a71 a81
                                                                    a91 a101
                                                                    a111) in
                                                             let uu___22 =
                                                               FStarC_TypeChecker_NBETerm.embed
                                                                 er cb r1 in
                                                             FStar_Pervasives_Native.Some
                                                               uu___22)))))))))))
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_12 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::[] ->
      let uu___12 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___12
        (fun a13 ->
           let uu___13 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___13
             (fun a21 ->
                let uu___14 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___14
                  (fun a31 ->
                     let uu___15 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___15
                       (fun a41 ->
                          let uu___16 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___16
                            (fun a51 ->
                               let uu___17 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___17
                                 (fun a61 ->
                                    let uu___18 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___18
                                      (fun a71 ->
                                         let uu___19 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___19
                                           (fun a81 ->
                                              let uu___20 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___20
                                                (fun a91 ->
                                                   let uu___21 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___21
                                                     (fun a101 ->
                                                        let uu___22 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___22
                                                          (fun a111 ->
                                                             let uu___23 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___23
                                                               (fun a121 ->
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
let mk_total_nbe_interpretation_13 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::[] ->
      let uu___13 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___13
        (fun a14 ->
           let uu___14 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___14
             (fun a21 ->
                let uu___15 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___15
                  (fun a31 ->
                     let uu___16 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___16
                       (fun a41 ->
                          let uu___17 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___17
                            (fun a51 ->
                               let uu___18 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___18
                                 (fun a61 ->
                                    let uu___19 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___19
                                      (fun a71 ->
                                         let uu___20 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___20
                                           (fun a81 ->
                                              let uu___21 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___21
                                                (fun a91 ->
                                                   let uu___22 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___22
                                                     (fun a101 ->
                                                        let uu___23 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___23
                                                          (fun a111 ->
                                                             let uu___24 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___24
                                                               (fun a121 ->
                                                                  let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___25
                                                                    (
                                                                    fun a131
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_14 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::[] ->
      let uu___14 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___14
        (fun a15 ->
           let uu___15 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___15
             (fun a21 ->
                let uu___16 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___16
                  (fun a31 ->
                     let uu___17 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___17
                       (fun a41 ->
                          let uu___18 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___18
                            (fun a51 ->
                               let uu___19 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___19
                                 (fun a61 ->
                                    let uu___20 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___20
                                      (fun a71 ->
                                         let uu___21 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___21
                                           (fun a81 ->
                                              let uu___22 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___22
                                                (fun a91 ->
                                                   let uu___23 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___23
                                                     (fun a101 ->
                                                        let uu___24 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___24
                                                          (fun a111 ->
                                                             let uu___25 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___25
                                                               (fun a121 ->
                                                                  let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___26
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_15 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
      't2 ->
        't3 ->
          't4 ->
            't5 ->
              't6 ->
                't7 ->
                  't8 ->
                    't9 -> 't10 -> 't11 -> 't12 -> 't13 -> 't14 -> 't15 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::[] ->
      let uu___15 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___15
        (fun a16 ->
           let uu___16 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___16
             (fun a21 ->
                let uu___17 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___17
                  (fun a31 ->
                     let uu___18 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___18
                       (fun a41 ->
                          let uu___19 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___19
                            (fun a51 ->
                               let uu___20 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___20
                                 (fun a61 ->
                                    let uu___21 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___21
                                      (fun a71 ->
                                         let uu___22 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___22
                                           (fun a81 ->
                                              let uu___23 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___23
                                                (fun a91 ->
                                                   let uu___24 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___24
                                                     (fun a101 ->
                                                        let uu___25 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___25
                                                          (fun a111 ->
                                                             let uu___26 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___26
                                                               (fun a121 ->
                                                                  let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___27
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___28
                                                                    (fun a141
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_16 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
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
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::[] ->
      let uu___16 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___16
        (fun a17 ->
           let uu___17 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___17
             (fun a21 ->
                let uu___18 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___18
                  (fun a31 ->
                     let uu___19 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___19
                       (fun a41 ->
                          let uu___20 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___20
                            (fun a51 ->
                               let uu___21 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___21
                                 (fun a61 ->
                                    let uu___22 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___22
                                      (fun a71 ->
                                         let uu___23 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___23
                                           (fun a81 ->
                                              let uu___24 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___24
                                                (fun a91 ->
                                                   let uu___25 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___25
                                                     (fun a101 ->
                                                        let uu___26 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___26
                                                          (fun a111 ->
                                                             let uu___27 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___27
                                                               (fun a121 ->
                                                                  let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___28
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___29
                                                                    (fun a141
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a151
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_17 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
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
                          't12 -> 't13 -> 't14 -> 't15 -> 't16 -> 't17 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::[] ->
      let uu___17 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___17
        (fun a18 ->
           let uu___18 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___18
             (fun a21 ->
                let uu___19 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___19
                  (fun a31 ->
                     let uu___20 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___20
                       (fun a41 ->
                          let uu___21 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___21
                            (fun a51 ->
                               let uu___22 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___22
                                 (fun a61 ->
                                    let uu___23 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___23
                                      (fun a71 ->
                                         let uu___24 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___24
                                           (fun a81 ->
                                              let uu___25 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___25
                                                (fun a91 ->
                                                   let uu___26 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___26
                                                     (fun a101 ->
                                                        let uu___27 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___27
                                                          (fun a111 ->
                                                             let uu___28 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___28
                                                               (fun a121 ->
                                                                  let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___29
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___30
                                                                    (fun a141
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a151
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a161
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_18 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
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
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (e18 : 't18 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::[] ->
      let uu___18 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___18
        (fun a19 ->
           let uu___19 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___19
             (fun a21 ->
                let uu___20 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___20
                  (fun a31 ->
                     let uu___21 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___21
                       (fun a41 ->
                          let uu___22 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___22
                            (fun a51 ->
                               let uu___23 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___23
                                 (fun a61 ->
                                    let uu___24 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___24
                                      (fun a71 ->
                                         let uu___25 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___25
                                           (fun a81 ->
                                              let uu___26 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___26
                                                (fun a91 ->
                                                   let uu___27 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___27
                                                     (fun a101 ->
                                                        let uu___28 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___28
                                                          (fun a111 ->
                                                             let uu___29 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___29
                                                               (fun a121 ->
                                                                  let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___30
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___31
                                                                    (fun a141
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a151
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a161
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a171
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_19 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
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
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (e18 : 't18 FStarC_TypeChecker_NBETerm.embedding)
  (e19 : 't19 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::[] ->
      let uu___19 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___19
        (fun a110 ->
           let uu___20 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___20
             (fun a21 ->
                let uu___21 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___21
                  (fun a31 ->
                     let uu___22 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___22
                       (fun a41 ->
                          let uu___23 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___23
                            (fun a51 ->
                               let uu___24 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___24
                                 (fun a61 ->
                                    let uu___25 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___25
                                      (fun a71 ->
                                         let uu___26 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___26
                                           (fun a81 ->
                                              let uu___27 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___27
                                                (fun a91 ->
                                                   let uu___28 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___28
                                                     (fun a101 ->
                                                        let uu___29 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___29
                                                          (fun a111 ->
                                                             let uu___30 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___30
                                                               (fun a121 ->
                                                                  let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___31
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___32
                                                                    (fun a141
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a151
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a161
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a171
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a181
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
let mk_total_nbe_interpretation_20 (name : Prims.string)
  (cb : FStarC_TypeChecker_NBETerm.nbe_cbs)
  (f :
    't1 ->
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
                                  't16 -> 't17 -> 't18 -> 't19 -> 't20 -> 'r)
  (e1 : 't1 FStarC_TypeChecker_NBETerm.embedding)
  (e2 : 't2 FStarC_TypeChecker_NBETerm.embedding)
  (e3 : 't3 FStarC_TypeChecker_NBETerm.embedding)
  (e4 : 't4 FStarC_TypeChecker_NBETerm.embedding)
  (e5 : 't5 FStarC_TypeChecker_NBETerm.embedding)
  (e6 : 't6 FStarC_TypeChecker_NBETerm.embedding)
  (e7 : 't7 FStarC_TypeChecker_NBETerm.embedding)
  (e8 : 't8 FStarC_TypeChecker_NBETerm.embedding)
  (e9 : 't9 FStarC_TypeChecker_NBETerm.embedding)
  (e10 : 't10 FStarC_TypeChecker_NBETerm.embedding)
  (e11 : 't11 FStarC_TypeChecker_NBETerm.embedding)
  (e12 : 't12 FStarC_TypeChecker_NBETerm.embedding)
  (e13 : 't13 FStarC_TypeChecker_NBETerm.embedding)
  (e14 : 't14 FStarC_TypeChecker_NBETerm.embedding)
  (e15 : 't15 FStarC_TypeChecker_NBETerm.embedding)
  (e16 : 't16 FStarC_TypeChecker_NBETerm.embedding)
  (e17 : 't17 FStarC_TypeChecker_NBETerm.embedding)
  (e18 : 't18 FStarC_TypeChecker_NBETerm.embedding)
  (e19 : 't19 FStarC_TypeChecker_NBETerm.embedding)
  (e20 : 't20 FStarC_TypeChecker_NBETerm.embedding)
  (er : 'r FStarC_TypeChecker_NBETerm.embedding)
  (us : FStarC_Syntax_Syntax.universes)
  (args : FStarC_TypeChecker_NBETerm.args) :
  FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
  match args with
  | (a1, uu___)::(a2, uu___1)::(a3, uu___2)::(a4, uu___3)::(a5, uu___4)::
      (a6, uu___5)::(a7, uu___6)::(a8, uu___7)::(a9, uu___8)::(a10, uu___9)::
      (a11, uu___10)::(a12, uu___11)::(a13, uu___12)::(a14, uu___13)::
      (a15, uu___14)::(a16, uu___15)::(a17, uu___16)::(a18, uu___17)::
      (a19, uu___18)::(a20, uu___19)::[] ->
      let uu___20 = FStarC_TypeChecker_NBETerm.unembed e1 cb a1 in
      FStarC_Option.bind uu___20
        (fun a110 ->
           let uu___21 = FStarC_TypeChecker_NBETerm.unembed e2 cb a2 in
           FStarC_Option.bind uu___21
             (fun a21 ->
                let uu___22 = FStarC_TypeChecker_NBETerm.unembed e3 cb a3 in
                FStarC_Option.bind uu___22
                  (fun a31 ->
                     let uu___23 =
                       FStarC_TypeChecker_NBETerm.unembed e4 cb a4 in
                     FStarC_Option.bind uu___23
                       (fun a41 ->
                          let uu___24 =
                            FStarC_TypeChecker_NBETerm.unembed e5 cb a5 in
                          FStarC_Option.bind uu___24
                            (fun a51 ->
                               let uu___25 =
                                 FStarC_TypeChecker_NBETerm.unembed e6 cb a6 in
                               FStarC_Option.bind uu___25
                                 (fun a61 ->
                                    let uu___26 =
                                      FStarC_TypeChecker_NBETerm.unembed e7
                                        cb a7 in
                                    FStarC_Option.bind uu___26
                                      (fun a71 ->
                                         let uu___27 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             e8 cb a8 in
                                         FStarC_Option.bind uu___27
                                           (fun a81 ->
                                              let uu___28 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  e9 cb a9 in
                                              FStarC_Option.bind uu___28
                                                (fun a91 ->
                                                   let uu___29 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       e10 cb a10 in
                                                   FStarC_Option.bind uu___29
                                                     (fun a101 ->
                                                        let uu___30 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            e11 cb a11 in
                                                        FStarC_Option.bind
                                                          uu___30
                                                          (fun a111 ->
                                                             let uu___31 =
                                                               FStarC_TypeChecker_NBETerm.unembed
                                                                 e12 cb a12 in
                                                             FStarC_Option.bind
                                                               uu___31
                                                               (fun a121 ->
                                                                  let uu___32
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e13 cb
                                                                    a13 in
                                                                  FStarC_Option.bind
                                                                    uu___32
                                                                    (
                                                                    fun a131
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e14 cb
                                                                    a14 in
                                                                    FStarC_Option.bind
                                                                    uu___33
                                                                    (fun a141
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e15 cb
                                                                    a15 in
                                                                    FStarC_Option.bind
                                                                    uu___34
                                                                    (fun a151
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e16 cb
                                                                    a16 in
                                                                    FStarC_Option.bind
                                                                    uu___35
                                                                    (fun a161
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e17 cb
                                                                    a17 in
                                                                    FStarC_Option.bind
                                                                    uu___36
                                                                    (fun a171
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e18 cb
                                                                    a18 in
                                                                    FStarC_Option.bind
                                                                    uu___37
                                                                    (fun a181
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e19 cb
                                                                    a19 in
                                                                    FStarC_Option.bind
                                                                    uu___38
                                                                    (fun a191
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    e20 cb
                                                                    a20 in
                                                                    FStarC_Option.bind
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
  | uu___ -> FStar_Pervasives_Native.None
