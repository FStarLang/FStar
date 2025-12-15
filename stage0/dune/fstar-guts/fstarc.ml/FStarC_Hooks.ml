open Prims
let lazy_chooser (k : FStarC_Syntax_Syntax.lazy_kind)
  (i : FStarC_Syntax_Syntax.lazyinfo) : FStarC_Syntax_Syntax.term=
  match k with
  | FStarC_Syntax_Syntax.BadLazy -> failwith "lazy chooser: got a BadLazy"
  | FStarC_Syntax_Syntax.Lazy_bv ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_bv i
  | FStarC_Syntax_Syntax.Lazy_namedv ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_namedv i
  | FStarC_Syntax_Syntax.Lazy_binder ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_binder i
  | FStarC_Syntax_Syntax.Lazy_letbinding ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_letbinding i
  | FStarC_Syntax_Syntax.Lazy_optionstate ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_optionstate i
  | FStarC_Syntax_Syntax.Lazy_fvar ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_fvar i
  | FStarC_Syntax_Syntax.Lazy_comp ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_comp i
  | FStarC_Syntax_Syntax.Lazy_env ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_env i
  | FStarC_Syntax_Syntax.Lazy_sigelt ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_sigelt i
  | FStarC_Syntax_Syntax.Lazy_universe ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_universe i
  | FStarC_Syntax_Syntax.Lazy_proofstate ->
      FStarC_Tactics_Embedding.unfold_lazy_proofstate i
  | FStarC_Syntax_Syntax.Lazy_ref_proofstate ->
      FStarC_Tactics_Embedding.unfold_lazy_ref_proofstate i
  | FStarC_Syntax_Syntax.Lazy_goal ->
      FStarC_Tactics_Embedding.unfold_lazy_goal i
  | FStarC_Syntax_Syntax.Lazy_doc ->
      FStarC_Reflection_V2_Embeddings.unfold_lazy_doc i
  | FStarC_Syntax_Syntax.Lazy_uvar ->
      FStarC_Syntax_Util.exp_string "((uvar))"
  | FStarC_Syntax_Syntax.Lazy_universe_uvar ->
      FStarC_Syntax_Util.exp_string "((universe_uvar))"
  | FStarC_Syntax_Syntax.Lazy_issue ->
      FStarC_Syntax_Util.exp_string "((issue))"
  | FStarC_Syntax_Syntax.Lazy_ident ->
      FStarC_Syntax_Util.exp_string "((ident))"
  | FStarC_Syntax_Syntax.Lazy_tref ->
      FStarC_Syntax_Util.exp_string "((tref))"
  | FStarC_Syntax_Syntax.Lazy_embedding (uu___, t) -> FStarC_Thunk.force t
  | FStarC_Syntax_Syntax.Lazy_extension s ->
      let uu___ = FStarC_Format.fmt1 "((extension %s))" s in
      FStarC_Syntax_Util.exp_string uu___
let uu___0 : unit=
  FStarC_Effect.op_Colon_Equals
    FStarC_Syntax_DsEnv.ugly_sigelt_to_string_hook
    (FStarC_Class_Show.show FStarC_Syntax_Print.showable_sigelt);
  FStarC_Errors.set_parse_warn_error FStarC_Parser_ParseIt.parse_warn_error;
  FStarC_Effect.op_Colon_Equals FStarC_Syntax_Syntax.lazy_chooser
    (FStar_Pervasives_Native.Some lazy_chooser);
  FStarC_Effect.op_Colon_Equals FStarC_Syntax_Util.tts_f
    (FStar_Pervasives_Native.Some
       (FStarC_Class_Show.show FStarC_Syntax_Print.showable_term));
  FStarC_Effect.op_Colon_Equals FStarC_Syntax_Util.ttd_f
    (FStar_Pervasives_Native.Some
       (FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term));
  FStarC_Effect.op_Colon_Equals
    FStarC_TypeChecker_Normalize.unembed_binder_knot
    (FStar_Pervasives_Native.Some FStarC_Reflection_V2_Embeddings.e_binder);
  FStarC_List.iter FStarC_Tactics_Interpreter.register_tactic_primitive_step
    FStarC_Tactics_V1_Primops.ops;
  FStarC_List.iter FStarC_Tactics_Interpreter.register_tactic_primitive_step
    FStarC_Tactics_V2_Primops.ops
