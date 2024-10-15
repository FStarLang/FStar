open Prims
type 'a withinfo_t = {
  v: 'a ;
  p: FStarC_Compiler_Range_Type.range }[@@deriving yojson,show]
let __proj__Mkwithinfo_t__item__v : 'a . 'a withinfo_t -> 'a =
  fun projectee -> match projectee with | { v; p;_} -> v
let __proj__Mkwithinfo_t__item__p :
  'a . 'a withinfo_t -> FStarC_Compiler_Range_Type.range =
  fun projectee -> match projectee with | { v; p;_} -> p
type var = FStarC_Ident.lident withinfo_t[@@deriving yojson,show]
type sconst = FStarC_Const.sconst[@@deriving yojson,show]
type pragma =
  | ShowOptions 
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | PrintEffectsGraph [@@deriving yojson,show]
let (uu___is_ShowOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ShowOptions -> true | uu___ -> false
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | SetOptions _0 -> true | uu___ -> false
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee -> match projectee with | SetOptions _0 -> _0
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ResetOptions _0 -> true | uu___ -> false
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | ResetOptions _0 -> _0
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PushOptions _0 -> true | uu___ -> false
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PushOptions _0 -> _0
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee -> match projectee with | PopOptions -> true | uu___ -> false
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartSolver -> true | uu___ -> false
let (uu___is_PrintEffectsGraph : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PrintEffectsGraph -> true | uu___ -> false
let (pragma_to_string : pragma -> Prims.string) =
  fun p ->
    match p with
    | ShowOptions -> "#show-options"
    | ResetOptions (FStar_Pervasives_Native.None) -> "#reset-options"
    | ResetOptions (FStar_Pervasives_Native.Some s) ->
        FStarC_Compiler_Util.format1 "#reset-options \"%s\"" s
    | SetOptions s -> FStarC_Compiler_Util.format1 "#set-options \"%s\"" s
    | PushOptions (FStar_Pervasives_Native.None) -> "#push-options"
    | PushOptions (FStar_Pervasives_Native.Some s) ->
        FStarC_Compiler_Util.format1 "#push-options \"%s\"" s
    | RestartSolver -> "#restart-solver"
    | PrintEffectsGraph -> "#print-effects-graph"
    | PopOptions -> "#pop-options"
let (showable_pragma : pragma FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = pragma_to_string }
type 'a memo =
  (('a FStar_Pervasives_Native.option FStarC_Compiler_Effect.ref)[@printer
                                                                   fun fmt ->
                                                                    fun _ ->
                                                                    Format.pp_print_string
                                                                    fmt
                                                                    "None"])
[@@deriving yojson,show]
type emb_typ =
  | ET_abstract 
  | ET_fun of (emb_typ * emb_typ) 
  | ET_app of (Prims.string * emb_typ Prims.list) 
let (uu___is_ET_abstract : emb_typ -> Prims.bool) =
  fun projectee ->
    match projectee with | ET_abstract -> true | uu___ -> false
let (uu___is_ET_fun : emb_typ -> Prims.bool) =
  fun projectee -> match projectee with | ET_fun _0 -> true | uu___ -> false
let (__proj__ET_fun__item___0 : emb_typ -> (emb_typ * emb_typ)) =
  fun projectee -> match projectee with | ET_fun _0 -> _0
let (uu___is_ET_app : emb_typ -> Prims.bool) =
  fun projectee -> match projectee with | ET_app _0 -> true | uu___ -> false
let (__proj__ET_app__item___0 :
  emb_typ -> (Prims.string * emb_typ Prims.list)) =
  fun projectee -> match projectee with | ET_app _0 -> _0
type version = {
  major: Prims.int ;
  minor: Prims.int }[@@deriving yojson,show]
let (__proj__Mkversion__item__major : version -> Prims.int) =
  fun projectee -> match projectee with | { major; minor;_} -> major
let (__proj__Mkversion__item__minor : version -> Prims.int) =
  fun projectee -> match projectee with | { major; minor;_} -> minor
type universe =
  | U_zero 
  | U_succ of universe 
  | U_max of universe Prims.list 
  | U_bvar of Prims.int 
  | U_name of FStarC_Ident.ident 
  | U_unif of (universe FStar_Pervasives_Native.option
  FStarC_Unionfind.p_uvar * version * FStarC_Compiler_Range_Type.range) 
  | U_unknown [@@deriving yojson,show]
let (uu___is_U_zero : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_zero -> true | uu___ -> false
let (uu___is_U_succ : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_succ _0 -> true | uu___ -> false
let (__proj__U_succ__item___0 : universe -> universe) =
  fun projectee -> match projectee with | U_succ _0 -> _0
let (uu___is_U_max : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_max _0 -> true | uu___ -> false
let (__proj__U_max__item___0 : universe -> universe Prims.list) =
  fun projectee -> match projectee with | U_max _0 -> _0
let (uu___is_U_bvar : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_bvar _0 -> true | uu___ -> false
let (__proj__U_bvar__item___0 : universe -> Prims.int) =
  fun projectee -> match projectee with | U_bvar _0 -> _0
let (uu___is_U_name : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_name _0 -> true | uu___ -> false
let (__proj__U_name__item___0 : universe -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | U_name _0 -> _0
let (uu___is_U_unif : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_unif _0 -> true | uu___ -> false
let (__proj__U_unif__item___0 :
  universe ->
    (universe FStar_Pervasives_Native.option FStarC_Unionfind.p_uvar *
      version * FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | U_unif _0 -> _0
let (uu___is_U_unknown : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_unknown -> true | uu___ -> false
type univ_name = FStarC_Ident.ident[@@deriving yojson,show]
type universe_uvar =
  (universe FStar_Pervasives_Native.option FStarC_Unionfind.p_uvar * version
    * FStarC_Compiler_Range_Type.range)[@@deriving yojson,show]
type univ_names = univ_name Prims.list[@@deriving yojson,show]
type universes = universe Prims.list[@@deriving yojson,show]
type monad_name = FStarC_Ident.lident[@@deriving yojson,show]
type quote_kind =
  | Quote_static 
  | Quote_dynamic [@@deriving yojson,show]
let (uu___is_Quote_static : quote_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote_static -> true | uu___ -> false
let (uu___is_Quote_dynamic : quote_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote_dynamic -> true | uu___ -> false
type maybe_set_use_range =
  | NoUseRange 
  | SomeUseRange of FStarC_Compiler_Range_Type.range [@@deriving yojson,show]
let (uu___is_NoUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee -> match projectee with | NoUseRange -> true | uu___ -> false
let (uu___is_SomeUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee ->
    match projectee with | SomeUseRange _0 -> true | uu___ -> false
let (__proj__SomeUseRange__item___0 :
  maybe_set_use_range -> FStarC_Compiler_Range_Type.range) =
  fun projectee -> match projectee with | SomeUseRange _0 -> _0
type delta_depth =
  | Delta_constant_at_level of Prims.int 
  | Delta_equational_at_level of Prims.int 
  | Delta_abstract of delta_depth [@@deriving yojson,show]
let (uu___is_Delta_constant_at_level : delta_depth -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Delta_constant_at_level _0 -> true
    | uu___ -> false
let (__proj__Delta_constant_at_level__item___0 : delta_depth -> Prims.int) =
  fun projectee -> match projectee with | Delta_constant_at_level _0 -> _0
let (uu___is_Delta_equational_at_level : delta_depth -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Delta_equational_at_level _0 -> true
    | uu___ -> false
let (__proj__Delta_equational_at_level__item___0 : delta_depth -> Prims.int)
  =
  fun projectee -> match projectee with | Delta_equational_at_level _0 -> _0
let (uu___is_Delta_abstract : delta_depth -> Prims.bool) =
  fun projectee ->
    match projectee with | Delta_abstract _0 -> true | uu___ -> false
let (__proj__Delta_abstract__item___0 : delta_depth -> delta_depth) =
  fun projectee -> match projectee with | Delta_abstract _0 -> _0
type should_check_uvar =
  | Allow_unresolved of Prims.string 
  | Allow_untyped of Prims.string 
  | Allow_ghost of Prims.string 
  | Strict 
  | Already_checked [@@deriving yojson,show]
let (uu___is_Allow_unresolved : should_check_uvar -> Prims.bool) =
  fun projectee ->
    match projectee with | Allow_unresolved _0 -> true | uu___ -> false
let (__proj__Allow_unresolved__item___0 : should_check_uvar -> Prims.string)
  = fun projectee -> match projectee with | Allow_unresolved _0 -> _0
let (uu___is_Allow_untyped : should_check_uvar -> Prims.bool) =
  fun projectee ->
    match projectee with | Allow_untyped _0 -> true | uu___ -> false
let (__proj__Allow_untyped__item___0 : should_check_uvar -> Prims.string) =
  fun projectee -> match projectee with | Allow_untyped _0 -> _0
let (uu___is_Allow_ghost : should_check_uvar -> Prims.bool) =
  fun projectee ->
    match projectee with | Allow_ghost _0 -> true | uu___ -> false
let (__proj__Allow_ghost__item___0 : should_check_uvar -> Prims.string) =
  fun projectee -> match projectee with | Allow_ghost _0 -> _0
let (uu___is_Strict : should_check_uvar -> Prims.bool) =
  fun projectee -> match projectee with | Strict -> true | uu___ -> false
let (uu___is_Already_checked : should_check_uvar -> Prims.bool) =
  fun projectee ->
    match projectee with | Already_checked -> true | uu___ -> false
type positivity_qualifier =
  | BinderStrictlyPositive 
  | BinderUnused 
let (uu___is_BinderStrictlyPositive : positivity_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | BinderStrictlyPositive -> true | uu___ -> false
let (uu___is_BinderUnused : positivity_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | BinderUnused -> true | uu___ -> false
type term'__Tm_abs__payload =
  {
  bs: binder Prims.list ;
  body: term' syntax ;
  rc_opt: residual_comp FStar_Pervasives_Native.option }
and term'__Tm_arrow__payload = {
  bs1: binder Prims.list ;
  comp: comp' syntax }
and term'__Tm_refine__payload = {
  b: bv ;
  phi: term' syntax }
and term'__Tm_app__payload =
  {
  hd: term' syntax ;
  args:
    (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list }
and term'__Tm_match__payload =
  {
  scrutinee: term' syntax ;
  ret_opt:
    (binder * ((term' syntax, comp' syntax) FStar_Pervasives.either * term'
      syntax FStar_Pervasives_Native.option * Prims.bool))
      FStar_Pervasives_Native.option
    ;
  brs:
    (pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term'
      syntax) Prims.list
    ;
  rc_opt1: residual_comp FStar_Pervasives_Native.option }
and term'__Tm_ascribed__payload =
  {
  tm: term' syntax ;
  asc:
    ((term' syntax, comp' syntax) FStar_Pervasives.either * term' syntax
      FStar_Pervasives_Native.option * Prims.bool)
    ;
  eff_opt: FStarC_Ident.lident FStar_Pervasives_Native.option }
and term'__Tm_let__payload =
  {
  lbs: (Prims.bool * letbinding Prims.list) ;
  body1: term' syntax }
and term'__Tm_delayed__payload =
  {
  tm1: term' syntax ;
  substs: (subst_elt Prims.list Prims.list * maybe_set_use_range) }
and term'__Tm_meta__payload = {
  tm2: term' syntax ;
  meta: metadata }
and term' =
  | Tm_bvar of bv 
  | Tm_name of bv 
  | Tm_fvar of fv 
  | Tm_uinst of (term' syntax * universes) 
  | Tm_constant of sconst 
  | Tm_type of universe 
  | Tm_abs of term'__Tm_abs__payload 
  | Tm_arrow of term'__Tm_arrow__payload 
  | Tm_refine of term'__Tm_refine__payload 
  | Tm_app of term'__Tm_app__payload 
  | Tm_match of term'__Tm_match__payload 
  | Tm_ascribed of term'__Tm_ascribed__payload 
  | Tm_let of term'__Tm_let__payload 
  | Tm_uvar of (ctx_uvar * (subst_elt Prims.list Prims.list *
  maybe_set_use_range)) 
  | Tm_delayed of term'__Tm_delayed__payload 
  | Tm_meta of term'__Tm_meta__payload 
  | Tm_lazy of lazyinfo 
  | Tm_quoted of (term' syntax * quoteinfo) 
  | Tm_unknown 
and ctx_uvar =
  {
  ctx_uvar_head:
    ((term' syntax FStar_Pervasives_Native.option * uvar_decoration)
      FStarC_Unionfind.p_uvar * version * FStarC_Compiler_Range_Type.range)
    ;
  ctx_uvar_gamma: binding Prims.list ;
  ctx_uvar_binders: binder Prims.list ;
  ctx_uvar_reason: Prims.string ;
  ctx_uvar_range: FStarC_Compiler_Range_Type.range ;
  ctx_uvar_meta: ctx_uvar_meta_t FStar_Pervasives_Native.option }
and ctx_uvar_meta_t =
  | Ctx_uvar_meta_tac of term' syntax 
  | Ctx_uvar_meta_attr of term' syntax 
and uvar_decoration =
  {
  uvar_decoration_typ: term' syntax ;
  uvar_decoration_typedness_depends_on: ctx_uvar Prims.list ;
  uvar_decoration_should_check: should_check_uvar ;
  uvar_decoration_should_unrefine: Prims.bool }
and pat' =
  | Pat_constant of sconst 
  | Pat_cons of (fv * universes FStar_Pervasives_Native.option * (pat'
  withinfo_t * Prims.bool) Prims.list) 
  | Pat_var of bv 
  | Pat_dot_term of term' syntax FStar_Pervasives_Native.option 
and letbinding =
  {
  lbname: (bv, fv) FStar_Pervasives.either ;
  lbunivs: univ_name Prims.list ;
  lbtyp: term' syntax ;
  lbeff: FStarC_Ident.lident ;
  lbdef: term' syntax ;
  lbattrs: term' syntax Prims.list ;
  lbpos: FStarC_Compiler_Range_Type.range }
and quoteinfo =
  {
  qkind: quote_kind ;
  antiquotations: (Prims.int * term' syntax Prims.list) }
and comp_typ =
  {
  comp_univs: universes ;
  effect_name: FStarC_Ident.lident ;
  result_typ: term' syntax ;
  effect_args:
    (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list ;
  flags: cflag Prims.list }
and comp' =
  | Total of term' syntax 
  | GTotal of term' syntax 
  | Comp of comp_typ 
and binder =
  {
  binder_bv: bv ;
  binder_qual: binder_qualifier FStar_Pervasives_Native.option ;
  binder_positivity: positivity_qualifier FStar_Pervasives_Native.option ;
  binder_attrs: term' syntax Prims.list }
and decreases_order =
  | Decreases_lex of term' syntax Prims.list 
  | Decreases_wf of (term' syntax * term' syntax) 
and cflag =
  | TOTAL 
  | MLEFFECT 
  | LEMMA 
  | RETURN 
  | PARTIAL_RETURN 
  | SOMETRIVIAL 
  | TRIVIAL_POSTCONDITION 
  | SHOULD_NOT_INLINE 
  | CPS 
  | DECREASES of decreases_order 
and metadata =
  | Meta_pattern of (term' syntax Prims.list * (term' syntax * arg_qualifier
  FStar_Pervasives_Native.option) Prims.list Prims.list) 
  | Meta_named of FStarC_Ident.lident 
  | Meta_labeled of (FStarC_Pprint.document Prims.list *
  FStarC_Compiler_Range_Type.range * Prims.bool) 
  | Meta_desugared of meta_source_info 
  | Meta_monadic of (monad_name * term' syntax) 
  | Meta_monadic_lift of (monad_name * monad_name * term' syntax) 
and meta_source_info =
  | Sequence 
  | Primop 
  | Masked_effect 
  | Meta_smt_pat 
  | Machine_integer of (FStarC_Const.signedness * FStarC_Const.width) 
and fv_qual =
  | Data_ctor 
  | Record_projector of (FStarC_Ident.lident * FStarC_Ident.ident) 
  | Record_ctor of (FStarC_Ident.lident * FStarC_Ident.ident Prims.list) 
  | Unresolved_projector of fv FStar_Pervasives_Native.option 
  | Unresolved_constructor of unresolved_constructor 
and unresolved_constructor =
  {
  uc_base_term: Prims.bool ;
  uc_typename: FStarC_Ident.lident FStar_Pervasives_Native.option ;
  uc_fields: FStarC_Ident.lident Prims.list }
and subst_elt =
  | DB of (Prims.int * bv) 
  | DT of (Prims.int * term' syntax) 
  | NM of (bv * Prims.int) 
  | NT of (bv * term' syntax) 
  | UN of (Prims.int * universe) 
  | UD of (univ_name * Prims.int) 
and 'a syntax =
  {
  n: 'a ;
  pos: FStarC_Compiler_Range_Type.range ;
  vars: free_vars memo ;
  hash_code: FStarC_Hash.hash_code memo }
and bv = {
  ppname: FStarC_Ident.ident ;
  index: Prims.int ;
  sort: term' syntax }
and fv = {
  fv_name: var ;
  fv_qual: fv_qual FStar_Pervasives_Native.option }
and free_vars =
  {
  free_names: bv FStarC_Compiler_FlatSet.t ;
  free_uvars: ctx_uvar FStarC_Compiler_FlatSet.t ;
  free_univs: universe_uvar FStarC_Compiler_FlatSet.t ;
  free_univ_names: univ_name FStarC_Compiler_FlatSet.t }
and residual_comp =
  {
  residual_effect: FStarC_Ident.lident ;
  residual_typ: term' syntax FStar_Pervasives_Native.option ;
  residual_flags: cflag Prims.list }
and lazyinfo =
  {
  blob: FStarC_Dyn.dyn ;
  lkind: lazy_kind ;
  ltyp: term' syntax ;
  rng: FStarC_Compiler_Range_Type.range }
and lazy_kind =
  | BadLazy 
  | Lazy_bv 
  | Lazy_namedv 
  | Lazy_binder 
  | Lazy_optionstate 
  | Lazy_fvar 
  | Lazy_comp 
  | Lazy_env 
  | Lazy_proofstate 
  | Lazy_goal 
  | Lazy_sigelt 
  | Lazy_uvar 
  | Lazy_letbinding 
  | Lazy_embedding of (emb_typ * term' syntax FStarC_Thunk.t) 
  | Lazy_universe 
  | Lazy_universe_uvar 
  | Lazy_issue 
  | Lazy_ident 
  | Lazy_doc 
  | Lazy_extension of Prims.string 
  | Lazy_tref 
and binding =
  | Binding_var of bv 
  | Binding_lid of (FStarC_Ident.lident * (univ_names * term' syntax)) 
  | Binding_univ of univ_name 
and binder_qualifier =
  | Implicit of Prims.bool 
  | Meta of term' syntax 
  | Equality 
and arg_qualifier =
  {
  aqual_implicit: Prims.bool ;
  aqual_attributes: term' syntax Prims.list }
let (__proj__Mkterm'__Tm_abs__payload__item__bs :
  term'__Tm_abs__payload -> binder Prims.list) =
  fun projectee -> match projectee with | { bs; body; rc_opt;_} -> bs
let (__proj__Mkterm'__Tm_abs__payload__item__body :
  term'__Tm_abs__payload -> term' syntax) =
  fun projectee -> match projectee with | { bs; body; rc_opt;_} -> body
let (__proj__Mkterm'__Tm_abs__payload__item__rc_opt :
  term'__Tm_abs__payload -> residual_comp FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { bs; body; rc_opt;_} -> rc_opt
let (__proj__Mkterm'__Tm_arrow__payload__item__bs :
  term'__Tm_arrow__payload -> binder Prims.list) =
  fun projectee -> match projectee with | { bs1 = bs; comp;_} -> bs
let (__proj__Mkterm'__Tm_arrow__payload__item__comp :
  term'__Tm_arrow__payload -> comp' syntax) =
  fun projectee -> match projectee with | { bs1 = bs; comp;_} -> comp
let (__proj__Mkterm'__Tm_refine__payload__item__b :
  term'__Tm_refine__payload -> bv) =
  fun projectee -> match projectee with | { b; phi;_} -> b
let (__proj__Mkterm'__Tm_refine__payload__item__phi :
  term'__Tm_refine__payload -> term' syntax) =
  fun projectee -> match projectee with | { b; phi;_} -> phi
let (__proj__Mkterm'__Tm_app__payload__item__hd :
  term'__Tm_app__payload -> term' syntax) =
  fun projectee -> match projectee with | { hd; args;_} -> hd
let (__proj__Mkterm'__Tm_app__payload__item__args :
  term'__Tm_app__payload ->
    (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list)
  = fun projectee -> match projectee with | { hd; args;_} -> args
let (__proj__Mkterm'__Tm_match__payload__item__scrutinee :
  term'__Tm_match__payload -> term' syntax) =
  fun projectee ->
    match projectee with
    | { scrutinee; ret_opt; brs; rc_opt1 = rc_opt;_} -> scrutinee
let (__proj__Mkterm'__Tm_match__payload__item__ret_opt :
  term'__Tm_match__payload ->
    (binder * ((term' syntax, comp' syntax) FStar_Pervasives.either * term'
      syntax FStar_Pervasives_Native.option * Prims.bool))
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { scrutinee; ret_opt; brs; rc_opt1 = rc_opt;_} -> ret_opt
let (__proj__Mkterm'__Tm_match__payload__item__brs :
  term'__Tm_match__payload ->
    (pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term'
      syntax) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { scrutinee; ret_opt; brs; rc_opt1 = rc_opt;_} -> brs
let (__proj__Mkterm'__Tm_match__payload__item__rc_opt :
  term'__Tm_match__payload -> residual_comp FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { scrutinee; ret_opt; brs; rc_opt1 = rc_opt;_} -> rc_opt
let (__proj__Mkterm'__Tm_ascribed__payload__item__tm :
  term'__Tm_ascribed__payload -> term' syntax) =
  fun projectee -> match projectee with | { tm; asc; eff_opt;_} -> tm
let (__proj__Mkterm'__Tm_ascribed__payload__item__asc :
  term'__Tm_ascribed__payload ->
    ((term' syntax, comp' syntax) FStar_Pervasives.either * term' syntax
      FStar_Pervasives_Native.option * Prims.bool))
  = fun projectee -> match projectee with | { tm; asc; eff_opt;_} -> asc
let (__proj__Mkterm'__Tm_ascribed__payload__item__eff_opt :
  term'__Tm_ascribed__payload ->
    FStarC_Ident.lident FStar_Pervasives_Native.option)
  = fun projectee -> match projectee with | { tm; asc; eff_opt;_} -> eff_opt
let (__proj__Mkterm'__Tm_let__payload__item__lbs :
  term'__Tm_let__payload -> (Prims.bool * letbinding Prims.list)) =
  fun projectee -> match projectee with | { lbs; body1 = body;_} -> lbs
let (__proj__Mkterm'__Tm_let__payload__item__body :
  term'__Tm_let__payload -> term' syntax) =
  fun projectee -> match projectee with | { lbs; body1 = body;_} -> body
let (__proj__Mkterm'__Tm_delayed__payload__item__tm :
  term'__Tm_delayed__payload -> term' syntax) =
  fun projectee -> match projectee with | { tm1 = tm; substs;_} -> tm
let (__proj__Mkterm'__Tm_delayed__payload__item__substs :
  term'__Tm_delayed__payload ->
    (subst_elt Prims.list Prims.list * maybe_set_use_range))
  = fun projectee -> match projectee with | { tm1 = tm; substs;_} -> substs
let (__proj__Mkterm'__Tm_meta__payload__item__tm :
  term'__Tm_meta__payload -> term' syntax) =
  fun projectee -> match projectee with | { tm2 = tm; meta;_} -> tm
let (__proj__Mkterm'__Tm_meta__payload__item__meta :
  term'__Tm_meta__payload -> metadata) =
  fun projectee -> match projectee with | { tm2 = tm; meta;_} -> meta
let (uu___is_Tm_bvar : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_bvar _0 -> true | uu___ -> false
let (__proj__Tm_bvar__item___0 : term' -> bv) =
  fun projectee -> match projectee with | Tm_bvar _0 -> _0
let (uu___is_Tm_name : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_name _0 -> true | uu___ -> false
let (__proj__Tm_name__item___0 : term' -> bv) =
  fun projectee -> match projectee with | Tm_name _0 -> _0
let (uu___is_Tm_fvar : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_fvar _0 -> true | uu___ -> false
let (__proj__Tm_fvar__item___0 : term' -> fv) =
  fun projectee -> match projectee with | Tm_fvar _0 -> _0
let (uu___is_Tm_uinst : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_uinst _0 -> true | uu___ -> false
let (__proj__Tm_uinst__item___0 : term' -> (term' syntax * universes)) =
  fun projectee -> match projectee with | Tm_uinst _0 -> _0
let (uu___is_Tm_constant : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_constant _0 -> true | uu___ -> false
let (__proj__Tm_constant__item___0 : term' -> sconst) =
  fun projectee -> match projectee with | Tm_constant _0 -> _0
let (uu___is_Tm_type : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_type _0 -> true | uu___ -> false
let (__proj__Tm_type__item___0 : term' -> universe) =
  fun projectee -> match projectee with | Tm_type _0 -> _0
let (uu___is_Tm_abs : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_abs _0 -> true | uu___ -> false
let (__proj__Tm_abs__item___0 : term' -> term'__Tm_abs__payload) =
  fun projectee -> match projectee with | Tm_abs _0 -> _0
let (uu___is_Tm_arrow : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_arrow _0 -> true | uu___ -> false
let (__proj__Tm_arrow__item___0 : term' -> term'__Tm_arrow__payload) =
  fun projectee -> match projectee with | Tm_arrow _0 -> _0
let (uu___is_Tm_refine : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_refine _0 -> true | uu___ -> false
let (__proj__Tm_refine__item___0 : term' -> term'__Tm_refine__payload) =
  fun projectee -> match projectee with | Tm_refine _0 -> _0
let (uu___is_Tm_app : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_app _0 -> true | uu___ -> false
let (__proj__Tm_app__item___0 : term' -> term'__Tm_app__payload) =
  fun projectee -> match projectee with | Tm_app _0 -> _0
let (uu___is_Tm_match : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_match _0 -> true | uu___ -> false
let (__proj__Tm_match__item___0 : term' -> term'__Tm_match__payload) =
  fun projectee -> match projectee with | Tm_match _0 -> _0
let (uu___is_Tm_ascribed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_ascribed _0 -> true | uu___ -> false
let (__proj__Tm_ascribed__item___0 : term' -> term'__Tm_ascribed__payload) =
  fun projectee -> match projectee with | Tm_ascribed _0 -> _0
let (uu___is_Tm_let : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_let _0 -> true | uu___ -> false
let (__proj__Tm_let__item___0 : term' -> term'__Tm_let__payload) =
  fun projectee -> match projectee with | Tm_let _0 -> _0
let (uu___is_Tm_uvar : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_uvar _0 -> true | uu___ -> false
let (__proj__Tm_uvar__item___0 :
  term' ->
    (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range)))
  = fun projectee -> match projectee with | Tm_uvar _0 -> _0
let (uu___is_Tm_delayed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_delayed _0 -> true | uu___ -> false
let (__proj__Tm_delayed__item___0 : term' -> term'__Tm_delayed__payload) =
  fun projectee -> match projectee with | Tm_delayed _0 -> _0
let (uu___is_Tm_meta : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_meta _0 -> true | uu___ -> false
let (__proj__Tm_meta__item___0 : term' -> term'__Tm_meta__payload) =
  fun projectee -> match projectee with | Tm_meta _0 -> _0
let (uu___is_Tm_lazy : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_lazy _0 -> true | uu___ -> false
let (__proj__Tm_lazy__item___0 : term' -> lazyinfo) =
  fun projectee -> match projectee with | Tm_lazy _0 -> _0
let (uu___is_Tm_quoted : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_quoted _0 -> true | uu___ -> false
let (__proj__Tm_quoted__item___0 : term' -> (term' syntax * quoteinfo)) =
  fun projectee -> match projectee with | Tm_quoted _0 -> _0
let (uu___is_Tm_unknown : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_unknown -> true | uu___ -> false
let (__proj__Mkctx_uvar__item__ctx_uvar_head :
  ctx_uvar ->
    ((term' syntax FStar_Pervasives_Native.option * uvar_decoration)
      FStarC_Unionfind.p_uvar * version * FStarC_Compiler_Range_Type.range))
  =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_reason;
        ctx_uvar_range; ctx_uvar_meta;_} -> ctx_uvar_head
let (__proj__Mkctx_uvar__item__ctx_uvar_gamma :
  ctx_uvar -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_reason;
        ctx_uvar_range; ctx_uvar_meta;_} -> ctx_uvar_gamma
let (__proj__Mkctx_uvar__item__ctx_uvar_binders :
  ctx_uvar -> binder Prims.list) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_reason;
        ctx_uvar_range; ctx_uvar_meta;_} -> ctx_uvar_binders
let (__proj__Mkctx_uvar__item__ctx_uvar_reason : ctx_uvar -> Prims.string) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_reason;
        ctx_uvar_range; ctx_uvar_meta;_} -> ctx_uvar_reason
let (__proj__Mkctx_uvar__item__ctx_uvar_range :
  ctx_uvar -> FStarC_Compiler_Range_Type.range) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_reason;
        ctx_uvar_range; ctx_uvar_meta;_} -> ctx_uvar_range
let (__proj__Mkctx_uvar__item__ctx_uvar_meta :
  ctx_uvar -> ctx_uvar_meta_t FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_reason;
        ctx_uvar_range; ctx_uvar_meta;_} -> ctx_uvar_meta
let (uu___is_Ctx_uvar_meta_tac : ctx_uvar_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Ctx_uvar_meta_tac _0 -> true | uu___ -> false
let (__proj__Ctx_uvar_meta_tac__item___0 : ctx_uvar_meta_t -> term' syntax) =
  fun projectee -> match projectee with | Ctx_uvar_meta_tac _0 -> _0
let (uu___is_Ctx_uvar_meta_attr : ctx_uvar_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Ctx_uvar_meta_attr _0 -> true | uu___ -> false
let (__proj__Ctx_uvar_meta_attr__item___0 : ctx_uvar_meta_t -> term' syntax)
  = fun projectee -> match projectee with | Ctx_uvar_meta_attr _0 -> _0
let (__proj__Mkuvar_decoration__item__uvar_decoration_typ :
  uvar_decoration -> term' syntax) =
  fun projectee ->
    match projectee with
    | { uvar_decoration_typ; uvar_decoration_typedness_depends_on;
        uvar_decoration_should_check; uvar_decoration_should_unrefine;_} ->
        uvar_decoration_typ
let (__proj__Mkuvar_decoration__item__uvar_decoration_typedness_depends_on :
  uvar_decoration -> ctx_uvar Prims.list) =
  fun projectee ->
    match projectee with
    | { uvar_decoration_typ; uvar_decoration_typedness_depends_on;
        uvar_decoration_should_check; uvar_decoration_should_unrefine;_} ->
        uvar_decoration_typedness_depends_on
let (__proj__Mkuvar_decoration__item__uvar_decoration_should_check :
  uvar_decoration -> should_check_uvar) =
  fun projectee ->
    match projectee with
    | { uvar_decoration_typ; uvar_decoration_typedness_depends_on;
        uvar_decoration_should_check; uvar_decoration_should_unrefine;_} ->
        uvar_decoration_should_check
let (__proj__Mkuvar_decoration__item__uvar_decoration_should_unrefine :
  uvar_decoration -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { uvar_decoration_typ; uvar_decoration_typedness_depends_on;
        uvar_decoration_should_check; uvar_decoration_should_unrefine;_} ->
        uvar_decoration_should_unrefine
let (uu___is_Pat_constant : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_constant _0 -> true | uu___ -> false
let (__proj__Pat_constant__item___0 : pat' -> sconst) =
  fun projectee -> match projectee with | Pat_constant _0 -> _0
let (uu___is_Pat_cons : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_cons _0 -> true | uu___ -> false
let (__proj__Pat_cons__item___0 :
  pat' ->
    (fv * universes FStar_Pervasives_Native.option * (pat' withinfo_t *
      Prims.bool) Prims.list))
  = fun projectee -> match projectee with | Pat_cons _0 -> _0
let (uu___is_Pat_var : pat' -> Prims.bool) =
  fun projectee -> match projectee with | Pat_var _0 -> true | uu___ -> false
let (__proj__Pat_var__item___0 : pat' -> bv) =
  fun projectee -> match projectee with | Pat_var _0 -> _0
let (uu___is_Pat_dot_term : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_dot_term _0 -> true | uu___ -> false
let (__proj__Pat_dot_term__item___0 :
  pat' -> term' syntax FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Pat_dot_term _0 -> _0
let (__proj__Mkletbinding__item__lbname :
  letbinding -> (bv, fv) FStar_Pervasives.either) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbname
let (__proj__Mkletbinding__item__lbunivs :
  letbinding -> univ_name Prims.list) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbunivs
let (__proj__Mkletbinding__item__lbtyp : letbinding -> term' syntax) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbtyp
let (__proj__Mkletbinding__item__lbeff : letbinding -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbeff
let (__proj__Mkletbinding__item__lbdef : letbinding -> term' syntax) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbdef
let (__proj__Mkletbinding__item__lbattrs :
  letbinding -> term' syntax Prims.list) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbattrs
let (__proj__Mkletbinding__item__lbpos :
  letbinding -> FStarC_Compiler_Range_Type.range) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbpos
let (__proj__Mkquoteinfo__item__qkind : quoteinfo -> quote_kind) =
  fun projectee -> match projectee with | { qkind; antiquotations;_} -> qkind
let (__proj__Mkquoteinfo__item__antiquotations :
  quoteinfo -> (Prims.int * term' syntax Prims.list)) =
  fun projectee ->
    match projectee with | { qkind; antiquotations;_} -> antiquotations
let (__proj__Mkcomp_typ__item__comp_univs : comp_typ -> universes) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStarC_Ident.lident)
  =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_name
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> term' syntax) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        result_typ
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ ->
    (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_args
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} -> flags
let (uu___is_Total : comp' -> Prims.bool) =
  fun projectee -> match projectee with | Total _0 -> true | uu___ -> false
let (__proj__Total__item___0 : comp' -> term' syntax) =
  fun projectee -> match projectee with | Total _0 -> _0
let (uu___is_GTotal : comp' -> Prims.bool) =
  fun projectee -> match projectee with | GTotal _0 -> true | uu___ -> false
let (__proj__GTotal__item___0 : comp' -> term' syntax) =
  fun projectee -> match projectee with | GTotal _0 -> _0
let (uu___is_Comp : comp' -> Prims.bool) =
  fun projectee -> match projectee with | Comp _0 -> true | uu___ -> false
let (__proj__Comp__item___0 : comp' -> comp_typ) =
  fun projectee -> match projectee with | Comp _0 -> _0
let (__proj__Mkbinder__item__binder_bv : binder -> bv) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_positivity; binder_attrs;_} ->
        binder_bv
let (__proj__Mkbinder__item__binder_qual :
  binder -> binder_qualifier FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_positivity; binder_attrs;_} ->
        binder_qual
let (__proj__Mkbinder__item__binder_positivity :
  binder -> positivity_qualifier FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_positivity; binder_attrs;_} ->
        binder_positivity
let (__proj__Mkbinder__item__binder_attrs :
  binder -> term' syntax Prims.list) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_positivity; binder_attrs;_} ->
        binder_attrs
let (uu___is_Decreases_lex : decreases_order -> Prims.bool) =
  fun projectee ->
    match projectee with | Decreases_lex _0 -> true | uu___ -> false
let (__proj__Decreases_lex__item___0 :
  decreases_order -> term' syntax Prims.list) =
  fun projectee -> match projectee with | Decreases_lex _0 -> _0
let (uu___is_Decreases_wf : decreases_order -> Prims.bool) =
  fun projectee ->
    match projectee with | Decreases_wf _0 -> true | uu___ -> false
let (__proj__Decreases_wf__item___0 :
  decreases_order -> (term' syntax * term' syntax)) =
  fun projectee -> match projectee with | Decreases_wf _0 -> _0
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee -> match projectee with | TOTAL -> true | uu___ -> false
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee -> match projectee with | MLEFFECT -> true | uu___ -> false
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee -> match projectee with | LEMMA -> true | uu___ -> false
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee -> match projectee with | RETURN -> true | uu___ -> false
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | PARTIAL_RETURN -> true | uu___ -> false
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SOMETRIVIAL -> true | uu___ -> false
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | TRIVIAL_POSTCONDITION -> true | uu___ -> false
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOULD_NOT_INLINE -> true | uu___ -> false
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee -> match projectee with | CPS -> true | uu___ -> false
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES _0 -> true | uu___ -> false
let (__proj__DECREASES__item___0 : cflag -> decreases_order) =
  fun projectee -> match projectee with | DECREASES _0 -> _0
let (uu___is_Meta_pattern : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_pattern _0 -> true | uu___ -> false
let (__proj__Meta_pattern__item___0 :
  metadata ->
    (term' syntax Prims.list * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list Prims.list))
  = fun projectee -> match projectee with | Meta_pattern _0 -> _0
let (uu___is_Meta_named : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_named _0 -> true | uu___ -> false
let (__proj__Meta_named__item___0 : metadata -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | Meta_named _0 -> _0
let (uu___is_Meta_labeled : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_labeled _0 -> true | uu___ -> false
let (__proj__Meta_labeled__item___0 :
  metadata ->
    (FStarC_Pprint.document Prims.list * FStarC_Compiler_Range_Type.range *
      Prims.bool))
  = fun projectee -> match projectee with | Meta_labeled _0 -> _0
let (uu___is_Meta_desugared : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_desugared _0 -> true | uu___ -> false
let (__proj__Meta_desugared__item___0 : metadata -> meta_source_info) =
  fun projectee -> match projectee with | Meta_desugared _0 -> _0
let (uu___is_Meta_monadic : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_monadic _0 -> true | uu___ -> false
let (__proj__Meta_monadic__item___0 :
  metadata -> (monad_name * term' syntax)) =
  fun projectee -> match projectee with | Meta_monadic _0 -> _0
let (uu___is_Meta_monadic_lift : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_monadic_lift _0 -> true | uu___ -> false
let (__proj__Meta_monadic_lift__item___0 :
  metadata -> (monad_name * monad_name * term' syntax)) =
  fun projectee -> match projectee with | Meta_monadic_lift _0 -> _0
let (uu___is_Sequence : meta_source_info -> Prims.bool) =
  fun projectee -> match projectee with | Sequence -> true | uu___ -> false
let (uu___is_Primop : meta_source_info -> Prims.bool) =
  fun projectee -> match projectee with | Primop -> true | uu___ -> false
let (uu___is_Masked_effect : meta_source_info -> Prims.bool) =
  fun projectee ->
    match projectee with | Masked_effect -> true | uu___ -> false
let (uu___is_Meta_smt_pat : meta_source_info -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_smt_pat -> true | uu___ -> false
let (uu___is_Machine_integer : meta_source_info -> Prims.bool) =
  fun projectee ->
    match projectee with | Machine_integer _0 -> true | uu___ -> false
let (__proj__Machine_integer__item___0 :
  meta_source_info -> (FStarC_Const.signedness * FStarC_Const.width)) =
  fun projectee -> match projectee with | Machine_integer _0 -> _0
let (uu___is_Data_ctor : fv_qual -> Prims.bool) =
  fun projectee -> match projectee with | Data_ctor -> true | uu___ -> false
let (uu___is_Record_projector : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_projector _0 -> true | uu___ -> false
let (__proj__Record_projector__item___0 :
  fv_qual -> (FStarC_Ident.lident * FStarC_Ident.ident)) =
  fun projectee -> match projectee with | Record_projector _0 -> _0
let (uu___is_Record_ctor : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_ctor _0 -> true | uu___ -> false
let (__proj__Record_ctor__item___0 :
  fv_qual -> (FStarC_Ident.lident * FStarC_Ident.ident Prims.list)) =
  fun projectee -> match projectee with | Record_ctor _0 -> _0
let (uu___is_Unresolved_projector : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Unresolved_projector _0 -> true | uu___ -> false
let (__proj__Unresolved_projector__item___0 :
  fv_qual -> fv FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Unresolved_projector _0 -> _0
let (uu___is_Unresolved_constructor : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Unresolved_constructor _0 -> true | uu___ -> false
let (__proj__Unresolved_constructor__item___0 :
  fv_qual -> unresolved_constructor) =
  fun projectee -> match projectee with | Unresolved_constructor _0 -> _0
let (__proj__Mkunresolved_constructor__item__uc_base_term :
  unresolved_constructor -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { uc_base_term; uc_typename; uc_fields;_} -> uc_base_term
let (__proj__Mkunresolved_constructor__item__uc_typename :
  unresolved_constructor ->
    FStarC_Ident.lident FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { uc_base_term; uc_typename; uc_fields;_} -> uc_typename
let (__proj__Mkunresolved_constructor__item__uc_fields :
  unresolved_constructor -> FStarC_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with
    | { uc_base_term; uc_typename; uc_fields;_} -> uc_fields
let (uu___is_DB : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | DB _0 -> true | uu___ -> false
let (__proj__DB__item___0 : subst_elt -> (Prims.int * bv)) =
  fun projectee -> match projectee with | DB _0 -> _0
let (uu___is_DT : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | DT _0 -> true | uu___ -> false
let (__proj__DT__item___0 : subst_elt -> (Prims.int * term' syntax)) =
  fun projectee -> match projectee with | DT _0 -> _0
let (uu___is_NM : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | NM _0 -> true | uu___ -> false
let (__proj__NM__item___0 : subst_elt -> (bv * Prims.int)) =
  fun projectee -> match projectee with | NM _0 -> _0
let (uu___is_NT : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | NT _0 -> true | uu___ -> false
let (__proj__NT__item___0 : subst_elt -> (bv * term' syntax)) =
  fun projectee -> match projectee with | NT _0 -> _0
let (uu___is_UN : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | UN _0 -> true | uu___ -> false
let (__proj__UN__item___0 : subst_elt -> (Prims.int * universe)) =
  fun projectee -> match projectee with | UN _0 -> _0
let (uu___is_UD : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | UD _0 -> true | uu___ -> false
let (__proj__UD__item___0 : subst_elt -> (univ_name * Prims.int)) =
  fun projectee -> match projectee with | UD _0 -> _0
let __proj__Mksyntax__item__n : 'a . 'a syntax -> 'a =
  fun projectee -> match projectee with | { n; pos; vars; hash_code;_} -> n
let __proj__Mksyntax__item__pos :
  'a . 'a syntax -> FStarC_Compiler_Range_Type.range =
  fun projectee -> match projectee with | { n; pos; vars; hash_code;_} -> pos
let __proj__Mksyntax__item__vars : 'a . 'a syntax -> free_vars memo =
  fun projectee ->
    match projectee with | { n; pos; vars; hash_code;_} -> vars
let __proj__Mksyntax__item__hash_code :
  'a . 'a syntax -> FStarC_Hash.hash_code memo =
  fun projectee ->
    match projectee with | { n; pos; vars; hash_code;_} -> hash_code
let (__proj__Mkbv__item__ppname : bv -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | { ppname; index; sort;_} -> ppname
let (__proj__Mkbv__item__index : bv -> Prims.int) =
  fun projectee -> match projectee with | { ppname; index; sort;_} -> index
let (__proj__Mkbv__item__sort : bv -> term' syntax) =
  fun projectee -> match projectee with | { ppname; index; sort;_} -> sort
let (__proj__Mkfv__item__fv_name : fv -> var) =
  fun projectee ->
    match projectee with | { fv_name; fv_qual = fv_qual1;_} -> fv_name
let (__proj__Mkfv__item__fv_qual :
  fv -> fv_qual FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { fv_name; fv_qual = fv_qual1;_} -> fv_qual1
let (__proj__Mkfree_vars__item__free_names :
  free_vars -> bv FStarC_Compiler_FlatSet.t) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_names
let (__proj__Mkfree_vars__item__free_uvars :
  free_vars -> ctx_uvar FStarC_Compiler_FlatSet.t) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_uvars
let (__proj__Mkfree_vars__item__free_univs :
  free_vars -> universe_uvar FStarC_Compiler_FlatSet.t) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_univs
let (__proj__Mkfree_vars__item__free_univ_names :
  free_vars -> univ_name FStarC_Compiler_FlatSet.t) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} ->
        free_univ_names
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_effect
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> term' syntax FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_typ
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
let (__proj__Mklazyinfo__item__blob : lazyinfo -> FStarC_Dyn.dyn) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> blob
let (__proj__Mklazyinfo__item__lkind : lazyinfo -> lazy_kind) =
  fun projectee ->
    match projectee with | { blob; lkind; ltyp; rng;_} -> lkind
let (__proj__Mklazyinfo__item__ltyp : lazyinfo -> term' syntax) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> ltyp
let (__proj__Mklazyinfo__item__rng :
  lazyinfo -> FStarC_Compiler_Range_Type.range) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> rng
let (uu___is_BadLazy : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | BadLazy -> true | uu___ -> false
let (uu___is_Lazy_bv : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_bv -> true | uu___ -> false
let (uu___is_Lazy_namedv : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_namedv -> true | uu___ -> false
let (uu___is_Lazy_binder : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_binder -> true | uu___ -> false
let (uu___is_Lazy_optionstate : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_optionstate -> true | uu___ -> false
let (uu___is_Lazy_fvar : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_fvar -> true | uu___ -> false
let (uu___is_Lazy_comp : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_comp -> true | uu___ -> false
let (uu___is_Lazy_env : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_env -> true | uu___ -> false
let (uu___is_Lazy_proofstate : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_proofstate -> true | uu___ -> false
let (uu___is_Lazy_goal : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_goal -> true | uu___ -> false
let (uu___is_Lazy_sigelt : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_sigelt -> true | uu___ -> false
let (uu___is_Lazy_uvar : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_uvar -> true | uu___ -> false
let (uu___is_Lazy_letbinding : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_letbinding -> true | uu___ -> false
let (uu___is_Lazy_embedding : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_embedding _0 -> true | uu___ -> false
let (__proj__Lazy_embedding__item___0 :
  lazy_kind -> (emb_typ * term' syntax FStarC_Thunk.t)) =
  fun projectee -> match projectee with | Lazy_embedding _0 -> _0
let (uu___is_Lazy_universe : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_universe -> true | uu___ -> false
let (uu___is_Lazy_universe_uvar : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_universe_uvar -> true | uu___ -> false
let (uu___is_Lazy_issue : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_issue -> true | uu___ -> false
let (uu___is_Lazy_ident : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_ident -> true | uu___ -> false
let (uu___is_Lazy_doc : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_doc -> true | uu___ -> false
let (uu___is_Lazy_extension : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_extension _0 -> true | uu___ -> false
let (__proj__Lazy_extension__item___0 : lazy_kind -> Prims.string) =
  fun projectee -> match projectee with | Lazy_extension _0 -> _0
let (uu___is_Lazy_tref : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_tref -> true | uu___ -> false
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_var _0 -> true | uu___ -> false
let (__proj__Binding_var__item___0 : binding -> bv) =
  fun projectee -> match projectee with | Binding_var _0 -> _0
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_lid _0 -> true | uu___ -> false
let (__proj__Binding_lid__item___0 :
  binding -> (FStarC_Ident.lident * (univ_names * term' syntax))) =
  fun projectee -> match projectee with | Binding_lid _0 -> _0
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_univ _0 -> true | uu___ -> false
let (__proj__Binding_univ__item___0 : binding -> univ_name) =
  fun projectee -> match projectee with | Binding_univ _0 -> _0
let (uu___is_Implicit : binder_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Implicit _0 -> true | uu___ -> false
let (__proj__Implicit__item___0 : binder_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Implicit _0 -> _0
let (uu___is_Meta : binder_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Meta _0 -> true | uu___ -> false
let (__proj__Meta__item___0 : binder_qualifier -> term' syntax) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Equality : binder_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Equality -> true | uu___ -> false
let (__proj__Mkarg_qualifier__item__aqual_implicit :
  arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { aqual_implicit; aqual_attributes;_} -> aqual_implicit
let (__proj__Mkarg_qualifier__item__aqual_attributes :
  arg_qualifier -> term' syntax Prims.list) =
  fun projectee ->
    match projectee with
    | { aqual_implicit; aqual_attributes;_} -> aqual_attributes
type subst_ts = (subst_elt Prims.list Prims.list * maybe_set_use_range)
type ctx_uvar_and_subst =
  (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range))
type term = term' syntax
type uvar =
  ((term' syntax FStar_Pervasives_Native.option * uvar_decoration)
    FStarC_Unionfind.p_uvar * version * FStarC_Compiler_Range_Type.range)
type uvars = ctx_uvar FStarC_Compiler_FlatSet.t
type comp = comp' syntax
type ascription =
  ((term' syntax, comp' syntax) FStar_Pervasives.either * term' syntax
    FStar_Pervasives_Native.option * Prims.bool)
type match_returns_ascription =
  (binder * ((term' syntax, comp' syntax) FStar_Pervasives.either * term'
    syntax FStar_Pervasives_Native.option * Prims.bool))
type pat = pat' withinfo_t
type branch =
  (pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term'
    syntax)
type antiquotations = (Prims.int * term' syntax Prims.list)
type typ = term' syntax
type aqual = arg_qualifier FStar_Pervasives_Native.option
type arg = (term' syntax * arg_qualifier FStar_Pervasives_Native.option)
type args =
  (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list
type binders = binder Prims.list
type lbname = (bv, fv) FStar_Pervasives.either
type letbindings = (Prims.bool * letbinding Prims.list)
type freenames = bv FStarC_Compiler_FlatSet.t
type attribute = term' syntax
type tscheme = (univ_name Prims.list * term' syntax)
type gamma = binding Prims.list
type bqual = binder_qualifier FStar_Pervasives_Native.option
type freenames_l = bv Prims.list
type formula = typ
type formulae = typ Prims.list
type qualifier =
  | Assumption 
  | New 
  | Private 
  | Unfold_for_unification_and_vcgen 
  | Irreducible 
  | Inline_for_extraction 
  | NoExtract 
  | Noeq 
  | Unopteq 
  | TotalEffect 
  | Logic 
  | Reifiable 
  | Reflectable of FStarC_Ident.lident 
  | Visible_default 
  | Discriminator of FStarC_Ident.lident 
  | Projector of (FStarC_Ident.lident * FStarC_Ident.ident) 
  | RecordType of (FStarC_Ident.ident Prims.list * FStarC_Ident.ident
  Prims.list) 
  | RecordConstructor of (FStarC_Ident.ident Prims.list * FStarC_Ident.ident
  Prims.list) 
  | Action of FStarC_Ident.lident 
  | ExceptionConstructor 
  | HasMaskedEffect 
  | Effect 
  | OnlyName 
  | InternalAssumption 
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Assumption -> true | uu___ -> false
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | New -> true | uu___ -> false
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Private -> true | uu___ -> false
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Unfold_for_unification_and_vcgen -> true
    | uu___ -> false
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Irreducible -> true | uu___ -> false
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Inline_for_extraction -> true | uu___ -> false
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | NoExtract -> true | uu___ -> false
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Noeq -> true | uu___ -> false
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Unopteq -> true | uu___ -> false
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TotalEffect -> true | uu___ -> false
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Logic -> true | uu___ -> false
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Reifiable -> true | uu___ -> false
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflectable _0 -> true | uu___ -> false
let (__proj__Reflectable__item___0 : qualifier -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | Reflectable _0 -> _0
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Visible_default -> true | uu___ -> false
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Discriminator _0 -> true | uu___ -> false
let (__proj__Discriminator__item___0 : qualifier -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | Discriminator _0 -> _0
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu___ -> false
let (__proj__Projector__item___0 :
  qualifier -> (FStarC_Ident.lident * FStarC_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordType _0 -> true | uu___ -> false
let (__proj__RecordType__item___0 :
  qualifier ->
    (FStarC_Ident.ident Prims.list * FStarC_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordType _0 -> _0
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordConstructor _0 -> true | uu___ -> false
let (__proj__RecordConstructor__item___0 :
  qualifier ->
    (FStarC_Ident.ident Prims.list * FStarC_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordConstructor _0 -> _0
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Action _0 -> true | uu___ -> false
let (__proj__Action__item___0 : qualifier -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | Action _0 -> _0
let (uu___is_ExceptionConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | ExceptionConstructor -> true | uu___ -> false
let (uu___is_HasMaskedEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | HasMaskedEffect -> true | uu___ -> false
let (uu___is_Effect : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Effect -> true | uu___ -> false
let (uu___is_OnlyName : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | OnlyName -> true | uu___ -> false
let (uu___is_InternalAssumption : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalAssumption -> true | uu___ -> false
let rec (emb_typ_to_string : emb_typ -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | ET_abstract -> "abstract"
    | ET_app (h, []) -> h
    | ET_app (h, args1) ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Compiler_List.map emb_typ_to_string args1 in
                FStarC_Compiler_String.concat " " uu___5 in
              Prims.strcat uu___4 ")" in
            Prims.strcat " " uu___3 in
          Prims.strcat h uu___2 in
        Prims.strcat "(" uu___1
    | ET_fun (a, b) ->
        let uu___1 =
          let uu___2 = emb_typ_to_string a in
          let uu___3 =
            let uu___4 = emb_typ_to_string b in Prims.strcat ") -> " uu___4 in
          Prims.strcat uu___2 uu___3 in
        Prims.strcat "(" uu___1
let (showable_emb_typ : emb_typ FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = emb_typ_to_string }
let rec (delta_depth_to_string : delta_depth -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Delta_constant_at_level i ->
        let uu___1 = FStarC_Compiler_Util.string_of_int i in
        Prims.strcat "Delta_constant_at_level " uu___1
    | Delta_equational_at_level i ->
        let uu___1 = FStarC_Compiler_Util.string_of_int i in
        Prims.strcat "Delta_equational_at_level " uu___1
    | Delta_abstract d ->
        let uu___1 =
          let uu___2 = delta_depth_to_string d in Prims.strcat uu___2 ")" in
        Prims.strcat "Delta_abstract (" uu___1
let (showable_delta_depth : delta_depth FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = delta_depth_to_string }
let (showable_should_check_uvar :
  should_check_uvar FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Allow_unresolved s -> Prims.strcat "Allow_unresolved " s
         | Allow_untyped s -> Prims.strcat "Allow_untyped " s
         | Allow_ghost s -> Prims.strcat "Allow_ghost " s
         | Strict -> "Strict"
         | Already_checked -> "Already_checked")
  }
let (lazy_chooser :
  (lazy_kind -> lazyinfo -> term) FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (cmp_qualifier : qualifier -> qualifier -> FStarC_Compiler_Order.order) =
  fun q1 ->
    fun q2 ->
      match (q1, q2) with
      | (Assumption, Assumption) -> FStarC_Compiler_Order.Eq
      | (New, New) -> FStarC_Compiler_Order.Eq
      | (Private, Private) -> FStarC_Compiler_Order.Eq
      | (Unfold_for_unification_and_vcgen, Unfold_for_unification_and_vcgen)
          -> FStarC_Compiler_Order.Eq
      | (Irreducible, Irreducible) -> FStarC_Compiler_Order.Eq
      | (Inline_for_extraction, Inline_for_extraction) ->
          FStarC_Compiler_Order.Eq
      | (NoExtract, NoExtract) -> FStarC_Compiler_Order.Eq
      | (Noeq, Noeq) -> FStarC_Compiler_Order.Eq
      | (Unopteq, Unopteq) -> FStarC_Compiler_Order.Eq
      | (TotalEffect, TotalEffect) -> FStarC_Compiler_Order.Eq
      | (Logic, Logic) -> FStarC_Compiler_Order.Eq
      | (Reifiable, Reifiable) -> FStarC_Compiler_Order.Eq
      | (Reflectable l1, Reflectable l2) ->
          FStarC_Class_Ord.cmp FStarC_Ident.ord_lident l1 l2
      | (Visible_default, Visible_default) -> FStarC_Compiler_Order.Eq
      | (Discriminator l1, Discriminator l2) ->
          FStarC_Class_Ord.cmp FStarC_Ident.ord_lident l1 l2
      | (Projector (l1, i1), Projector (l2, i2)) ->
          FStarC_Class_Ord.cmp
            (FStarC_Class_Ord.ord_tuple2 FStarC_Ident.ord_lident
               FStarC_Ident.ord_ident) (l1, i1) (l2, i2)
      | (RecordType (l1, i1), RecordType (l2, i2)) ->
          FStarC_Class_Ord.cmp
            (FStarC_Class_Ord.ord_tuple2
               (FStarC_Class_Ord.ord_list FStarC_Ident.ord_ident)
               (FStarC_Class_Ord.ord_list FStarC_Ident.ord_ident)) (l1, i1)
            (l2, i2)
      | (RecordConstructor (l1, i1), RecordConstructor (l2, i2)) ->
          FStarC_Class_Ord.cmp
            (FStarC_Class_Ord.ord_tuple2
               (FStarC_Class_Ord.ord_list FStarC_Ident.ord_ident)
               (FStarC_Class_Ord.ord_list FStarC_Ident.ord_ident)) (l1, i1)
            (l2, i2)
      | (Action l1, Action l2) ->
          FStarC_Class_Ord.cmp FStarC_Ident.ord_lident l1 l2
      | (ExceptionConstructor, ExceptionConstructor) ->
          FStarC_Compiler_Order.Eq
      | (HasMaskedEffect, HasMaskedEffect) -> FStarC_Compiler_Order.Eq
      | (Effect, Effect) -> FStarC_Compiler_Order.Eq
      | (OnlyName, OnlyName) -> FStarC_Compiler_Order.Eq
      | (InternalAssumption, InternalAssumption) -> FStarC_Compiler_Order.Eq
      | (Assumption, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Assumption) -> FStarC_Compiler_Order.Gt
      | (New, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, New) -> FStarC_Compiler_Order.Gt
      | (Private, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Private) -> FStarC_Compiler_Order.Gt
      | (Unfold_for_unification_and_vcgen, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Unfold_for_unification_and_vcgen) -> FStarC_Compiler_Order.Gt
      | (Irreducible, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Irreducible) -> FStarC_Compiler_Order.Gt
      | (Inline_for_extraction, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Inline_for_extraction) -> FStarC_Compiler_Order.Gt
      | (NoExtract, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, NoExtract) -> FStarC_Compiler_Order.Gt
      | (Noeq, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Noeq) -> FStarC_Compiler_Order.Gt
      | (Unopteq, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Unopteq) -> FStarC_Compiler_Order.Gt
      | (TotalEffect, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, TotalEffect) -> FStarC_Compiler_Order.Gt
      | (Logic, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Logic) -> FStarC_Compiler_Order.Gt
      | (Reifiable, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Reifiable) -> FStarC_Compiler_Order.Gt
      | (Reflectable uu___, uu___1) -> FStarC_Compiler_Order.Lt
      | (uu___, Reflectable uu___1) -> FStarC_Compiler_Order.Gt
      | (Visible_default, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Visible_default) -> FStarC_Compiler_Order.Gt
      | (Discriminator uu___, uu___1) -> FStarC_Compiler_Order.Lt
      | (uu___, Discriminator uu___1) -> FStarC_Compiler_Order.Gt
      | (Projector uu___, uu___1) -> FStarC_Compiler_Order.Lt
      | (uu___, Projector uu___1) -> FStarC_Compiler_Order.Gt
      | (RecordType uu___, uu___1) -> FStarC_Compiler_Order.Lt
      | (uu___, RecordType uu___1) -> FStarC_Compiler_Order.Gt
      | (RecordConstructor uu___, uu___1) -> FStarC_Compiler_Order.Lt
      | (uu___, RecordConstructor uu___1) -> FStarC_Compiler_Order.Gt
      | (Action uu___, uu___1) -> FStarC_Compiler_Order.Lt
      | (uu___, Action uu___1) -> FStarC_Compiler_Order.Gt
      | (ExceptionConstructor, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, ExceptionConstructor) -> FStarC_Compiler_Order.Gt
      | (HasMaskedEffect, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, HasMaskedEffect) -> FStarC_Compiler_Order.Gt
      | (Effect, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, Effect) -> FStarC_Compiler_Order.Gt
      | (OnlyName, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, OnlyName) -> FStarC_Compiler_Order.Gt
      | (InternalAssumption, uu___) -> FStarC_Compiler_Order.Lt
      | (uu___, InternalAssumption) -> FStarC_Compiler_Order.Gt
let (deq_qualifier : qualifier FStarC_Class_Deq.deq) =
  {
    FStarC_Class_Deq.op_Equals_Question =
      (fun q1 ->
         fun q2 ->
           let uu___ = cmp_qualifier q1 q2 in
           uu___ = FStarC_Compiler_Order.Eq)
  }
let (ord_qualifier : qualifier FStarC_Class_Ord.ord) =
  {
    FStarC_Class_Ord.super = deq_qualifier;
    FStarC_Class_Ord.cmp = cmp_qualifier
  }
let (is_internal_qualifier : qualifier -> Prims.bool) =
  fun q ->
    match q with
    | Visible_default -> true
    | Discriminator uu___ -> true
    | Projector uu___ -> true
    | RecordType uu___ -> true
    | RecordConstructor uu___ -> true
    | Action uu___ -> true
    | ExceptionConstructor -> true
    | HasMaskedEffect -> true
    | Effect -> true
    | OnlyName -> true
    | InternalAssumption -> true
    | uu___ -> false
type tycon = (FStarC_Ident.lident * binders * typ)
type monad_abbrev = {
  mabbrev: FStarC_Ident.lident ;
  parms: binders ;
  def: typ }
let (__proj__Mkmonad_abbrev__item__mabbrev :
  monad_abbrev -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | { mabbrev; parms; def;_} -> mabbrev
let (__proj__Mkmonad_abbrev__item__parms : monad_abbrev -> binders) =
  fun projectee -> match projectee with | { mabbrev; parms; def;_} -> parms
let (__proj__Mkmonad_abbrev__item__def : monad_abbrev -> typ) =
  fun projectee -> match projectee with | { mabbrev; parms; def;_} -> def
type indexed_effect_binder_kind =
  | Type_binder 
  | Substitutive_binder 
  | BindCont_no_abstraction_binder 
  | Range_binder 
  | Repr_binder 
  | Ad_hoc_binder 
let (uu___is_Type_binder : indexed_effect_binder_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Type_binder -> true | uu___ -> false
let (uu___is_Substitutive_binder : indexed_effect_binder_kind -> Prims.bool)
  =
  fun projectee ->
    match projectee with | Substitutive_binder -> true | uu___ -> false
let (uu___is_BindCont_no_abstraction_binder :
  indexed_effect_binder_kind -> Prims.bool) =
  fun projectee ->
    match projectee with
    | BindCont_no_abstraction_binder -> true
    | uu___ -> false
let (uu___is_Range_binder : indexed_effect_binder_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Range_binder -> true | uu___ -> false
let (uu___is_Repr_binder : indexed_effect_binder_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Repr_binder -> true | uu___ -> false
let (uu___is_Ad_hoc_binder : indexed_effect_binder_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Ad_hoc_binder -> true | uu___ -> false
let (showable_indexed_effect_binder_kind :
  indexed_effect_binder_kind FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Type_binder -> "Type_binder"
         | Substitutive_binder -> "Substitutive_binder"
         | BindCont_no_abstraction_binder -> "BindCont_no_abstraction_binder"
         | Range_binder -> "Range_binder"
         | Repr_binder -> "Repr_binder"
         | Ad_hoc_binder -> "Ad_hoc_binder")
  }
let (tagged_indexed_effect_binder_kind :
  indexed_effect_binder_kind FStarC_Class_Tagged.tagged) =
  {
    FStarC_Class_Tagged.tag_of =
      (fun uu___ ->
         match uu___ with
         | Type_binder -> "Type_binder"
         | Substitutive_binder -> "Substitutive_binder"
         | BindCont_no_abstraction_binder -> "BindCont_no_abstraction_binder"
         | Range_binder -> "Range_binder"
         | Repr_binder -> "Repr_binder"
         | Ad_hoc_binder -> "Ad_hoc_binder")
  }
type indexed_effect_combinator_kind =
  | Substitutive_combinator of indexed_effect_binder_kind Prims.list 
  | Substitutive_invariant_combinator 
  | Ad_hoc_combinator 
let (uu___is_Substitutive_combinator :
  indexed_effect_combinator_kind -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Substitutive_combinator _0 -> true
    | uu___ -> false
let (__proj__Substitutive_combinator__item___0 :
  indexed_effect_combinator_kind -> indexed_effect_binder_kind Prims.list) =
  fun projectee -> match projectee with | Substitutive_combinator _0 -> _0
let (uu___is_Substitutive_invariant_combinator :
  indexed_effect_combinator_kind -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Substitutive_invariant_combinator -> true
    | uu___ -> false
let (uu___is_Ad_hoc_combinator :
  indexed_effect_combinator_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Ad_hoc_combinator -> true | uu___ -> false
let (showable_indexed_effect_combinator_kind :
  indexed_effect_combinator_kind FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Substitutive_combinator ks ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    showable_indexed_effect_binder_kind) ks in
             Prims.strcat "Substitutive_combinator " uu___1
         | Substitutive_invariant_combinator ->
             "Substitutive_invariant_combinator"
         | Ad_hoc_combinator -> "Ad_hoc_combinator")
  }
let (tagged_indexed_effect_combinator_kind :
  indexed_effect_combinator_kind FStarC_Class_Tagged.tagged) =
  {
    FStarC_Class_Tagged.tag_of =
      (fun uu___ ->
         match uu___ with
         | Substitutive_combinator uu___1 -> "Substitutive_combinator"
         | Substitutive_invariant_combinator ->
             "Substitutive_invariant_combinator"
         | Ad_hoc_combinator -> "Ad_hoc_combinator")
  }
type sub_eff =
  {
  source: FStarC_Ident.lident ;
  target: FStarC_Ident.lident ;
  lift_wp: tscheme FStar_Pervasives_Native.option ;
  lift: tscheme FStar_Pervasives_Native.option ;
  kind: indexed_effect_combinator_kind FStar_Pervasives_Native.option }
let (__proj__Mksub_eff__item__source : sub_eff -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift; kind;_} -> source
let (__proj__Mksub_eff__item__target : sub_eff -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift; kind;_} -> target
let (__proj__Mksub_eff__item__lift_wp :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { source; target; lift_wp; lift; kind;_} -> lift_wp
let (__proj__Mksub_eff__item__lift :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift; kind;_} -> lift
let (__proj__Mksub_eff__item__kind :
  sub_eff -> indexed_effect_combinator_kind FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift; kind;_} -> kind
type action =
  {
  action_name: FStarC_Ident.lident ;
  action_unqualified_name: FStarC_Ident.ident ;
  action_univs: univ_names ;
  action_params: binders ;
  action_defn: term ;
  action_typ: typ }
let (__proj__Mkaction__item__action_name : action -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_name
let (__proj__Mkaction__item__action_unqualified_name :
  action -> FStarC_Ident.ident) =
  fun projectee ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_unqualified_name
let (__proj__Mkaction__item__action_univs : action -> univ_names) =
  fun projectee ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_univs
let (__proj__Mkaction__item__action_params : action -> binders) =
  fun projectee ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_params
let (__proj__Mkaction__item__action_defn : action -> term) =
  fun projectee ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_defn
let (__proj__Mkaction__item__action_typ : action -> typ) =
  fun projectee ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_typ
type wp_eff_combinators =
  {
  ret_wp: tscheme ;
  bind_wp: tscheme ;
  stronger: tscheme ;
  if_then_else: tscheme ;
  ite_wp: tscheme ;
  close_wp: tscheme ;
  trivial: tscheme ;
  repr: tscheme FStar_Pervasives_Native.option ;
  return_repr: tscheme FStar_Pervasives_Native.option ;
  bind_repr: tscheme FStar_Pervasives_Native.option }
let (__proj__Mkwp_eff_combinators__item__ret_wp :
  wp_eff_combinators -> tscheme) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> ret_wp
let (__proj__Mkwp_eff_combinators__item__bind_wp :
  wp_eff_combinators -> tscheme) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> bind_wp
let (__proj__Mkwp_eff_combinators__item__stronger :
  wp_eff_combinators -> tscheme) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> stronger
let (__proj__Mkwp_eff_combinators__item__if_then_else :
  wp_eff_combinators -> tscheme) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> if_then_else
let (__proj__Mkwp_eff_combinators__item__ite_wp :
  wp_eff_combinators -> tscheme) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> ite_wp
let (__proj__Mkwp_eff_combinators__item__close_wp :
  wp_eff_combinators -> tscheme) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> close_wp
let (__proj__Mkwp_eff_combinators__item__trivial :
  wp_eff_combinators -> tscheme) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> trivial
let (__proj__Mkwp_eff_combinators__item__repr :
  wp_eff_combinators -> tscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> repr
let (__proj__Mkwp_eff_combinators__item__return_repr :
  wp_eff_combinators -> tscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> return_repr
let (__proj__Mkwp_eff_combinators__item__bind_repr :
  wp_eff_combinators -> tscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ret_wp; bind_wp; stronger; if_then_else; ite_wp; close_wp; trivial;
        repr; return_repr; bind_repr;_} -> bind_repr
type layered_eff_combinators =
  {
  l_repr: (tscheme * tscheme) ;
  l_return: (tscheme * tscheme) ;
  l_bind:
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option)
    ;
  l_subcomp:
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option)
    ;
  l_if_then_else:
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option)
    ;
  l_close: (tscheme * tscheme) FStar_Pervasives_Native.option }
let (__proj__Mklayered_eff_combinators__item__l_repr :
  layered_eff_combinators -> (tscheme * tscheme)) =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else; l_close;_} ->
        l_repr
let (__proj__Mklayered_eff_combinators__item__l_return :
  layered_eff_combinators -> (tscheme * tscheme)) =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else; l_close;_} ->
        l_return
let (__proj__Mklayered_eff_combinators__item__l_bind :
  layered_eff_combinators ->
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else; l_close;_} ->
        l_bind
let (__proj__Mklayered_eff_combinators__item__l_subcomp :
  layered_eff_combinators ->
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else; l_close;_} ->
        l_subcomp
let (__proj__Mklayered_eff_combinators__item__l_if_then_else :
  layered_eff_combinators ->
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else; l_close;_} ->
        l_if_then_else
let (__proj__Mklayered_eff_combinators__item__l_close :
  layered_eff_combinators ->
    (tscheme * tscheme) FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else; l_close;_} ->
        l_close
type eff_combinators =
  | Primitive_eff of wp_eff_combinators 
  | DM4F_eff of wp_eff_combinators 
  | Layered_eff of layered_eff_combinators 
let (uu___is_Primitive_eff : eff_combinators -> Prims.bool) =
  fun projectee ->
    match projectee with | Primitive_eff _0 -> true | uu___ -> false
let (__proj__Primitive_eff__item___0 : eff_combinators -> wp_eff_combinators)
  = fun projectee -> match projectee with | Primitive_eff _0 -> _0
let (uu___is_DM4F_eff : eff_combinators -> Prims.bool) =
  fun projectee ->
    match projectee with | DM4F_eff _0 -> true | uu___ -> false
let (__proj__DM4F_eff__item___0 : eff_combinators -> wp_eff_combinators) =
  fun projectee -> match projectee with | DM4F_eff _0 -> _0
let (uu___is_Layered_eff : eff_combinators -> Prims.bool) =
  fun projectee ->
    match projectee with | Layered_eff _0 -> true | uu___ -> false
let (__proj__Layered_eff__item___0 :
  eff_combinators -> layered_eff_combinators) =
  fun projectee -> match projectee with | Layered_eff _0 -> _0
type effect_signature =
  | Layered_eff_sig of (Prims.int * tscheme) 
  | WP_eff_sig of tscheme 
let (uu___is_Layered_eff_sig : effect_signature -> Prims.bool) =
  fun projectee ->
    match projectee with | Layered_eff_sig _0 -> true | uu___ -> false
let (__proj__Layered_eff_sig__item___0 :
  effect_signature -> (Prims.int * tscheme)) =
  fun projectee -> match projectee with | Layered_eff_sig _0 -> _0
let (uu___is_WP_eff_sig : effect_signature -> Prims.bool) =
  fun projectee ->
    match projectee with | WP_eff_sig _0 -> true | uu___ -> false
let (__proj__WP_eff_sig__item___0 : effect_signature -> tscheme) =
  fun projectee -> match projectee with | WP_eff_sig _0 -> _0
type eff_extraction_mode =
  | Extract_none of Prims.string 
  | Extract_reify 
  | Extract_primitive 
let (uu___is_Extract_none : eff_extraction_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | Extract_none _0 -> true | uu___ -> false
let (__proj__Extract_none__item___0 : eff_extraction_mode -> Prims.string) =
  fun projectee -> match projectee with | Extract_none _0 -> _0
let (uu___is_Extract_reify : eff_extraction_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | Extract_reify -> true | uu___ -> false
let (uu___is_Extract_primitive : eff_extraction_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | Extract_primitive -> true | uu___ -> false
let (showable_eff_extraction_mode :
  eff_extraction_mode FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Extract_none s -> Prims.strcat "Extract_none " s
         | Extract_reify -> "Extract_reify"
         | Extract_primitive -> "Extract_primitive")
  }
let (tagged_eff_extraction_mode :
  eff_extraction_mode FStarC_Class_Tagged.tagged) =
  {
    FStarC_Class_Tagged.tag_of =
      (fun uu___ ->
         match uu___ with
         | Extract_none uu___1 -> "Extract_none"
         | Extract_reify -> "Extract_reify"
         | Extract_primitive -> "Extract_primitive")
  }
type eff_decl =
  {
  mname: FStarC_Ident.lident ;
  cattributes: cflag Prims.list ;
  univs: univ_names ;
  binders: binders ;
  signature: effect_signature ;
  combinators: eff_combinators ;
  actions: action Prims.list ;
  eff_attrs: attribute Prims.list ;
  extraction_mode: eff_extraction_mode }
let (__proj__Mkeff_decl__item__mname : eff_decl -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> mname
let (__proj__Mkeff_decl__item__cattributes : eff_decl -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> cattributes
let (__proj__Mkeff_decl__item__univs : eff_decl -> univ_names) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> univs
let (__proj__Mkeff_decl__item__binders : eff_decl -> binders) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> binders1
let (__proj__Mkeff_decl__item__signature : eff_decl -> effect_signature) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> signature
let (__proj__Mkeff_decl__item__combinators : eff_decl -> eff_combinators) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> combinators
let (__proj__Mkeff_decl__item__actions : eff_decl -> action Prims.list) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> actions
let (__proj__Mkeff_decl__item__eff_attrs : eff_decl -> attribute Prims.list)
  =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} -> eff_attrs
let (__proj__Mkeff_decl__item__extraction_mode :
  eff_decl -> eff_extraction_mode) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs; extraction_mode;_} ->
        extraction_mode
type sig_metadata =
  {
  sigmeta_active: Prims.bool ;
  sigmeta_fact_db_ids: Prims.string Prims.list ;
  sigmeta_admit: Prims.bool ;
  sigmeta_spliced: Prims.bool ;
  sigmeta_already_checked: Prims.bool ;
  sigmeta_extension_data: (Prims.string * FStarC_Dyn.dyn) Prims.list }
let (__proj__Mksig_metadata__item__sigmeta_active :
  sig_metadata -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit; sigmeta_spliced;
        sigmeta_already_checked; sigmeta_extension_data;_} -> sigmeta_active
let (__proj__Mksig_metadata__item__sigmeta_fact_db_ids :
  sig_metadata -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit; sigmeta_spliced;
        sigmeta_already_checked; sigmeta_extension_data;_} ->
        sigmeta_fact_db_ids
let (__proj__Mksig_metadata__item__sigmeta_admit :
  sig_metadata -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit; sigmeta_spliced;
        sigmeta_already_checked; sigmeta_extension_data;_} -> sigmeta_admit
let (__proj__Mksig_metadata__item__sigmeta_spliced :
  sig_metadata -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit; sigmeta_spliced;
        sigmeta_already_checked; sigmeta_extension_data;_} -> sigmeta_spliced
let (__proj__Mksig_metadata__item__sigmeta_already_checked :
  sig_metadata -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit; sigmeta_spliced;
        sigmeta_already_checked; sigmeta_extension_data;_} ->
        sigmeta_already_checked
let (__proj__Mksig_metadata__item__sigmeta_extension_data :
  sig_metadata -> (Prims.string * FStarC_Dyn.dyn) Prims.list) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit; sigmeta_spliced;
        sigmeta_already_checked; sigmeta_extension_data;_} ->
        sigmeta_extension_data
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu___ -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu___ -> false
type ident_alias = FStarC_Ident.ident FStar_Pervasives_Native.option
type restriction =
  | Unrestricted 
  | AllowList of (FStarC_Ident.ident * ident_alias) Prims.list 
let (uu___is_Unrestricted : restriction -> Prims.bool) =
  fun projectee ->
    match projectee with | Unrestricted -> true | uu___ -> false
let (uu___is_AllowList : restriction -> Prims.bool) =
  fun projectee ->
    match projectee with | AllowList _0 -> true | uu___ -> false
let (__proj__AllowList__item___0 :
  restriction -> (FStarC_Ident.ident * ident_alias) Prims.list) =
  fun projectee -> match projectee with | AllowList _0 -> _0
type open_module_or_namespace =
  (FStarC_Ident.lident * open_kind * restriction)
type module_abbrev = (FStarC_Ident.ident * FStarC_Ident.lident)
type sigelt'__Sig_inductive_typ__payload =
  {
  lid: FStarC_Ident.lident ;
  us: univ_names ;
  params: binders ;
  num_uniform_params: Prims.int FStar_Pervasives_Native.option ;
  t: typ ;
  mutuals: FStarC_Ident.lident Prims.list ;
  ds: FStarC_Ident.lident Prims.list ;
  injective_type_params: Prims.bool }
and sigelt'__Sig_bundle__payload =
  {
  ses: sigelt Prims.list ;
  lids: FStarC_Ident.lident Prims.list }
and sigelt'__Sig_datacon__payload =
  {
  lid1: FStarC_Ident.lident ;
  us1: univ_names ;
  t1: typ ;
  ty_lid: FStarC_Ident.lident ;
  num_ty_params: Prims.int ;
  mutuals1: FStarC_Ident.lident Prims.list ;
  injective_type_params1: Prims.bool }
and sigelt'__Sig_declare_typ__payload =
  {
  lid2: FStarC_Ident.lident ;
  us2: univ_names ;
  t2: typ }
and sigelt'__Sig_let__payload =
  {
  lbs1: letbindings ;
  lids1: FStarC_Ident.lident Prims.list }
and sigelt'__Sig_assume__payload =
  {
  lid3: FStarC_Ident.lident ;
  us3: univ_names ;
  phi1: formula }
and sigelt'__Sig_effect_abbrev__payload =
  {
  lid4: FStarC_Ident.lident ;
  us4: univ_names ;
  bs2: binders ;
  comp1: comp ;
  cflags: cflag Prims.list }
and sigelt'__Sig_splice__payload =
  {
  is_typed: Prims.bool ;
  lids2: FStarC_Ident.lident Prims.list ;
  tac: term }
and sigelt'__Sig_polymonadic_bind__payload =
  {
  m_lid: FStarC_Ident.lident ;
  n_lid: FStarC_Ident.lident ;
  p_lid: FStarC_Ident.lident ;
  tm3: tscheme ;
  typ: tscheme ;
  kind1: indexed_effect_combinator_kind FStar_Pervasives_Native.option }
and sigelt'__Sig_polymonadic_subcomp__payload =
  {
  m_lid1: FStarC_Ident.lident ;
  n_lid1: FStarC_Ident.lident ;
  tm4: tscheme ;
  typ1: tscheme ;
  kind2: indexed_effect_combinator_kind FStar_Pervasives_Native.option }
and sigelt'__Sig_fail__payload =
  {
  errs: Prims.int Prims.list ;
  fail_in_lax: Prims.bool ;
  ses1: sigelt Prims.list }
and sigelt' =
  | Sig_inductive_typ of sigelt'__Sig_inductive_typ__payload 
  | Sig_bundle of sigelt'__Sig_bundle__payload 
  | Sig_datacon of sigelt'__Sig_datacon__payload 
  | Sig_declare_typ of sigelt'__Sig_declare_typ__payload 
  | Sig_let of sigelt'__Sig_let__payload 
  | Sig_assume of sigelt'__Sig_assume__payload 
  | Sig_new_effect of eff_decl 
  | Sig_sub_effect of sub_eff 
  | Sig_effect_abbrev of sigelt'__Sig_effect_abbrev__payload 
  | Sig_pragma of pragma 
  | Sig_splice of sigelt'__Sig_splice__payload 
  | Sig_polymonadic_bind of sigelt'__Sig_polymonadic_bind__payload 
  | Sig_polymonadic_subcomp of sigelt'__Sig_polymonadic_subcomp__payload 
  | Sig_fail of sigelt'__Sig_fail__payload 
and sigelt =
  {
  sigel: sigelt' ;
  sigrng: FStarC_Compiler_Range_Type.range ;
  sigquals: qualifier Prims.list ;
  sigmeta: sig_metadata ;
  sigattrs: attribute Prims.list ;
  sigopens_and_abbrevs:
    (open_module_or_namespace, module_abbrev) FStar_Pervasives.either
      Prims.list
    ;
  sigopts: FStarC_VConfig.vconfig FStar_Pervasives_Native.option }
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__lid :
  sigelt'__Sig_inductive_typ__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> lid
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__us :
  sigelt'__Sig_inductive_typ__payload -> univ_names) =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> us
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__params :
  sigelt'__Sig_inductive_typ__payload -> binders) =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> params
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__num_uniform_params
  :
  sigelt'__Sig_inductive_typ__payload ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> num_uniform_params
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__t :
  sigelt'__Sig_inductive_typ__payload -> typ) =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> t
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__mutuals :
  sigelt'__Sig_inductive_typ__payload -> FStarC_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> mutuals
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__ds :
  sigelt'__Sig_inductive_typ__payload -> FStarC_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> ds
let (__proj__Mksigelt'__Sig_inductive_typ__payload__item__injective_type_params
  : sigelt'__Sig_inductive_typ__payload -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { lid; us; params; num_uniform_params; t; mutuals; ds;
        injective_type_params;_} -> injective_type_params
let (__proj__Mksigelt'__Sig_bundle__payload__item__ses :
  sigelt'__Sig_bundle__payload -> sigelt Prims.list) =
  fun projectee -> match projectee with | { ses; lids;_} -> ses
let (__proj__Mksigelt'__Sig_bundle__payload__item__lids :
  sigelt'__Sig_bundle__payload -> FStarC_Ident.lident Prims.list) =
  fun projectee -> match projectee with | { ses; lids;_} -> lids
let (__proj__Mksigelt'__Sig_datacon__payload__item__lid :
  sigelt'__Sig_datacon__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { lid1 = lid; us1 = us; t1 = t; ty_lid; num_ty_params;
        mutuals1 = mutuals; injective_type_params1 = injective_type_params;_}
        -> lid
let (__proj__Mksigelt'__Sig_datacon__payload__item__us :
  sigelt'__Sig_datacon__payload -> univ_names) =
  fun projectee ->
    match projectee with
    | { lid1 = lid; us1 = us; t1 = t; ty_lid; num_ty_params;
        mutuals1 = mutuals; injective_type_params1 = injective_type_params;_}
        -> us
let (__proj__Mksigelt'__Sig_datacon__payload__item__t :
  sigelt'__Sig_datacon__payload -> typ) =
  fun projectee ->
    match projectee with
    | { lid1 = lid; us1 = us; t1 = t; ty_lid; num_ty_params;
        mutuals1 = mutuals; injective_type_params1 = injective_type_params;_}
        -> t
let (__proj__Mksigelt'__Sig_datacon__payload__item__ty_lid :
  sigelt'__Sig_datacon__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { lid1 = lid; us1 = us; t1 = t; ty_lid; num_ty_params;
        mutuals1 = mutuals; injective_type_params1 = injective_type_params;_}
        -> ty_lid
let (__proj__Mksigelt'__Sig_datacon__payload__item__num_ty_params :
  sigelt'__Sig_datacon__payload -> Prims.int) =
  fun projectee ->
    match projectee with
    | { lid1 = lid; us1 = us; t1 = t; ty_lid; num_ty_params;
        mutuals1 = mutuals; injective_type_params1 = injective_type_params;_}
        -> num_ty_params
let (__proj__Mksigelt'__Sig_datacon__payload__item__mutuals :
  sigelt'__Sig_datacon__payload -> FStarC_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with
    | { lid1 = lid; us1 = us; t1 = t; ty_lid; num_ty_params;
        mutuals1 = mutuals; injective_type_params1 = injective_type_params;_}
        -> mutuals
let (__proj__Mksigelt'__Sig_datacon__payload__item__injective_type_params :
  sigelt'__Sig_datacon__payload -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { lid1 = lid; us1 = us; t1 = t; ty_lid; num_ty_params;
        mutuals1 = mutuals; injective_type_params1 = injective_type_params;_}
        -> injective_type_params
let (__proj__Mksigelt'__Sig_declare_typ__payload__item__lid :
  sigelt'__Sig_declare_typ__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with | { lid2 = lid; us2 = us; t2 = t;_} -> lid
let (__proj__Mksigelt'__Sig_declare_typ__payload__item__us :
  sigelt'__Sig_declare_typ__payload -> univ_names) =
  fun projectee ->
    match projectee with | { lid2 = lid; us2 = us; t2 = t;_} -> us
let (__proj__Mksigelt'__Sig_declare_typ__payload__item__t :
  sigelt'__Sig_declare_typ__payload -> typ) =
  fun projectee ->
    match projectee with | { lid2 = lid; us2 = us; t2 = t;_} -> t
let (__proj__Mksigelt'__Sig_let__payload__item__lbs :
  sigelt'__Sig_let__payload -> letbindings) =
  fun projectee ->
    match projectee with | { lbs1 = lbs; lids1 = lids;_} -> lbs
let (__proj__Mksigelt'__Sig_let__payload__item__lids :
  sigelt'__Sig_let__payload -> FStarC_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with | { lbs1 = lbs; lids1 = lids;_} -> lids
let (__proj__Mksigelt'__Sig_assume__payload__item__lid :
  sigelt'__Sig_assume__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with | { lid3 = lid; us3 = us; phi1 = phi;_} -> lid
let (__proj__Mksigelt'__Sig_assume__payload__item__us :
  sigelt'__Sig_assume__payload -> univ_names) =
  fun projectee ->
    match projectee with | { lid3 = lid; us3 = us; phi1 = phi;_} -> us
let (__proj__Mksigelt'__Sig_assume__payload__item__phi :
  sigelt'__Sig_assume__payload -> formula) =
  fun projectee ->
    match projectee with | { lid3 = lid; us3 = us; phi1 = phi;_} -> phi
let (__proj__Mksigelt'__Sig_effect_abbrev__payload__item__lid :
  sigelt'__Sig_effect_abbrev__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { lid4 = lid; us4 = us; bs2 = bs; comp1; cflags;_} -> lid
let (__proj__Mksigelt'__Sig_effect_abbrev__payload__item__us :
  sigelt'__Sig_effect_abbrev__payload -> univ_names) =
  fun projectee ->
    match projectee with
    | { lid4 = lid; us4 = us; bs2 = bs; comp1; cflags;_} -> us
let (__proj__Mksigelt'__Sig_effect_abbrev__payload__item__bs :
  sigelt'__Sig_effect_abbrev__payload -> binders) =
  fun projectee ->
    match projectee with
    | { lid4 = lid; us4 = us; bs2 = bs; comp1; cflags;_} -> bs
let (__proj__Mksigelt'__Sig_effect_abbrev__payload__item__comp :
  sigelt'__Sig_effect_abbrev__payload -> comp) =
  fun projectee ->
    match projectee with
    | { lid4 = lid; us4 = us; bs2 = bs; comp1; cflags;_} -> comp1
let (__proj__Mksigelt'__Sig_effect_abbrev__payload__item__cflags :
  sigelt'__Sig_effect_abbrev__payload -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { lid4 = lid; us4 = us; bs2 = bs; comp1; cflags;_} -> cflags
let (__proj__Mksigelt'__Sig_splice__payload__item__is_typed :
  sigelt'__Sig_splice__payload -> Prims.bool) =
  fun projectee ->
    match projectee with | { is_typed; lids2 = lids; tac;_} -> is_typed
let (__proj__Mksigelt'__Sig_splice__payload__item__lids :
  sigelt'__Sig_splice__payload -> FStarC_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with | { is_typed; lids2 = lids; tac;_} -> lids
let (__proj__Mksigelt'__Sig_splice__payload__item__tac :
  sigelt'__Sig_splice__payload -> term) =
  fun projectee ->
    match projectee with | { is_typed; lids2 = lids; tac;_} -> tac
let (__proj__Mksigelt'__Sig_polymonadic_bind__payload__item__m_lid :
  sigelt'__Sig_polymonadic_bind__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { m_lid; n_lid; p_lid; tm3 = tm; typ = typ1; kind1 = kind;_} -> m_lid
let (__proj__Mksigelt'__Sig_polymonadic_bind__payload__item__n_lid :
  sigelt'__Sig_polymonadic_bind__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { m_lid; n_lid; p_lid; tm3 = tm; typ = typ1; kind1 = kind;_} -> n_lid
let (__proj__Mksigelt'__Sig_polymonadic_bind__payload__item__p_lid :
  sigelt'__Sig_polymonadic_bind__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { m_lid; n_lid; p_lid; tm3 = tm; typ = typ1; kind1 = kind;_} -> p_lid
let (__proj__Mksigelt'__Sig_polymonadic_bind__payload__item__tm :
  sigelt'__Sig_polymonadic_bind__payload -> tscheme) =
  fun projectee ->
    match projectee with
    | { m_lid; n_lid; p_lid; tm3 = tm; typ = typ1; kind1 = kind;_} -> tm
let (__proj__Mksigelt'__Sig_polymonadic_bind__payload__item__typ :
  sigelt'__Sig_polymonadic_bind__payload -> tscheme) =
  fun projectee ->
    match projectee with
    | { m_lid; n_lid; p_lid; tm3 = tm; typ = typ1; kind1 = kind;_} -> typ1
let (__proj__Mksigelt'__Sig_polymonadic_bind__payload__item__kind :
  sigelt'__Sig_polymonadic_bind__payload ->
    indexed_effect_combinator_kind FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { m_lid; n_lid; p_lid; tm3 = tm; typ = typ1; kind1 = kind;_} -> kind
let (__proj__Mksigelt'__Sig_polymonadic_subcomp__payload__item__m_lid :
  sigelt'__Sig_polymonadic_subcomp__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { m_lid1 = m_lid; n_lid1 = n_lid; tm4 = tm; typ1; kind2 = kind;_} ->
        m_lid
let (__proj__Mksigelt'__Sig_polymonadic_subcomp__payload__item__n_lid :
  sigelt'__Sig_polymonadic_subcomp__payload -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { m_lid1 = m_lid; n_lid1 = n_lid; tm4 = tm; typ1; kind2 = kind;_} ->
        n_lid
let (__proj__Mksigelt'__Sig_polymonadic_subcomp__payload__item__tm :
  sigelt'__Sig_polymonadic_subcomp__payload -> tscheme) =
  fun projectee ->
    match projectee with
    | { m_lid1 = m_lid; n_lid1 = n_lid; tm4 = tm; typ1; kind2 = kind;_} -> tm
let (__proj__Mksigelt'__Sig_polymonadic_subcomp__payload__item__typ :
  sigelt'__Sig_polymonadic_subcomp__payload -> tscheme) =
  fun projectee ->
    match projectee with
    | { m_lid1 = m_lid; n_lid1 = n_lid; tm4 = tm; typ1; kind2 = kind;_} ->
        typ1
let (__proj__Mksigelt'__Sig_polymonadic_subcomp__payload__item__kind :
  sigelt'__Sig_polymonadic_subcomp__payload ->
    indexed_effect_combinator_kind FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { m_lid1 = m_lid; n_lid1 = n_lid; tm4 = tm; typ1; kind2 = kind;_} ->
        kind
let (__proj__Mksigelt'__Sig_fail__payload__item__errs :
  sigelt'__Sig_fail__payload -> Prims.int Prims.list) =
  fun projectee ->
    match projectee with | { errs; fail_in_lax; ses1 = ses;_} -> errs
let (__proj__Mksigelt'__Sig_fail__payload__item__fail_in_lax :
  sigelt'__Sig_fail__payload -> Prims.bool) =
  fun projectee ->
    match projectee with | { errs; fail_in_lax; ses1 = ses;_} -> fail_in_lax
let (__proj__Mksigelt'__Sig_fail__payload__item__ses :
  sigelt'__Sig_fail__payload -> sigelt Prims.list) =
  fun projectee ->
    match projectee with | { errs; fail_in_lax; ses1 = ses;_} -> ses
let (uu___is_Sig_inductive_typ : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_inductive_typ _0 -> true | uu___ -> false
let (__proj__Sig_inductive_typ__item___0 :
  sigelt' -> sigelt'__Sig_inductive_typ__payload) =
  fun projectee -> match projectee with | Sig_inductive_typ _0 -> _0
let (uu___is_Sig_bundle : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_bundle _0 -> true | uu___ -> false
let (__proj__Sig_bundle__item___0 : sigelt' -> sigelt'__Sig_bundle__payload)
  = fun projectee -> match projectee with | Sig_bundle _0 -> _0
let (uu___is_Sig_datacon : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_datacon _0 -> true | uu___ -> false
let (__proj__Sig_datacon__item___0 :
  sigelt' -> sigelt'__Sig_datacon__payload) =
  fun projectee -> match projectee with | Sig_datacon _0 -> _0
let (uu___is_Sig_declare_typ : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_declare_typ _0 -> true | uu___ -> false
let (__proj__Sig_declare_typ__item___0 :
  sigelt' -> sigelt'__Sig_declare_typ__payload) =
  fun projectee -> match projectee with | Sig_declare_typ _0 -> _0
let (uu___is_Sig_let : sigelt' -> Prims.bool) =
  fun projectee -> match projectee with | Sig_let _0 -> true | uu___ -> false
let (__proj__Sig_let__item___0 : sigelt' -> sigelt'__Sig_let__payload) =
  fun projectee -> match projectee with | Sig_let _0 -> _0
let (uu___is_Sig_assume : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_assume _0 -> true | uu___ -> false
let (__proj__Sig_assume__item___0 : sigelt' -> sigelt'__Sig_assume__payload)
  = fun projectee -> match projectee with | Sig_assume _0 -> _0
let (uu___is_Sig_new_effect : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_new_effect _0 -> true | uu___ -> false
let (__proj__Sig_new_effect__item___0 : sigelt' -> eff_decl) =
  fun projectee -> match projectee with | Sig_new_effect _0 -> _0
let (uu___is_Sig_sub_effect : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_sub_effect _0 -> true | uu___ -> false
let (__proj__Sig_sub_effect__item___0 : sigelt' -> sub_eff) =
  fun projectee -> match projectee with | Sig_sub_effect _0 -> _0
let (uu___is_Sig_effect_abbrev : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_effect_abbrev _0 -> true | uu___ -> false
let (__proj__Sig_effect_abbrev__item___0 :
  sigelt' -> sigelt'__Sig_effect_abbrev__payload) =
  fun projectee -> match projectee with | Sig_effect_abbrev _0 -> _0
let (uu___is_Sig_pragma : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_pragma _0 -> true | uu___ -> false
let (__proj__Sig_pragma__item___0 : sigelt' -> pragma) =
  fun projectee -> match projectee with | Sig_pragma _0 -> _0
let (uu___is_Sig_splice : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_splice _0 -> true | uu___ -> false
let (__proj__Sig_splice__item___0 : sigelt' -> sigelt'__Sig_splice__payload)
  = fun projectee -> match projectee with | Sig_splice _0 -> _0
let (uu___is_Sig_polymonadic_bind : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_polymonadic_bind _0 -> true | uu___ -> false
let (__proj__Sig_polymonadic_bind__item___0 :
  sigelt' -> sigelt'__Sig_polymonadic_bind__payload) =
  fun projectee -> match projectee with | Sig_polymonadic_bind _0 -> _0
let (uu___is_Sig_polymonadic_subcomp : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Sig_polymonadic_subcomp _0 -> true
    | uu___ -> false
let (__proj__Sig_polymonadic_subcomp__item___0 :
  sigelt' -> sigelt'__Sig_polymonadic_subcomp__payload) =
  fun projectee -> match projectee with | Sig_polymonadic_subcomp _0 -> _0
let (uu___is_Sig_fail : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_fail _0 -> true | uu___ -> false
let (__proj__Sig_fail__item___0 : sigelt' -> sigelt'__Sig_fail__payload) =
  fun projectee -> match projectee with | Sig_fail _0 -> _0
let (__proj__Mksigelt__item__sigel : sigelt -> sigelt') =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs;
        sigopts;_} -> sigel
let (__proj__Mksigelt__item__sigrng :
  sigelt -> FStarC_Compiler_Range_Type.range) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs;
        sigopts;_} -> sigrng
let (__proj__Mksigelt__item__sigquals : sigelt -> qualifier Prims.list) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs;
        sigopts;_} -> sigquals
let (__proj__Mksigelt__item__sigmeta : sigelt -> sig_metadata) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs;
        sigopts;_} -> sigmeta
let (__proj__Mksigelt__item__sigattrs : sigelt -> attribute Prims.list) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs;
        sigopts;_} -> sigattrs
let (__proj__Mksigelt__item__sigopens_and_abbrevs :
  sigelt ->
    (open_module_or_namespace, module_abbrev) FStar_Pervasives.either
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs;
        sigopts;_} -> sigopens_and_abbrevs
let (__proj__Mksigelt__item__sigopts :
  sigelt -> FStarC_VConfig.vconfig FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs;
        sigopts;_} -> sigopts
type sigelts = sigelt Prims.list
type modul =
  {
  name: FStarC_Ident.lident ;
  declarations: sigelts ;
  is_interface: Prims.bool }
let (__proj__Mkmodul__item__name : modul -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with | { name; declarations; is_interface;_} -> name
let (__proj__Mkmodul__item__declarations : modul -> sigelts) =
  fun projectee ->
    match projectee with
    | { name; declarations; is_interface;_} -> declarations
let (__proj__Mkmodul__item__is_interface : modul -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name; declarations; is_interface;_} -> is_interface
let (mod_name : modul -> FStarC_Ident.lident) = fun m -> m.name
let (contains_reflectable : qualifier Prims.list -> Prims.bool) =
  fun l ->
    FStarC_Compiler_Util.for_some
      (fun uu___ ->
         match uu___ with | Reflectable uu___1 -> true | uu___1 -> false) l
let withinfo : 'a . 'a -> FStarC_Compiler_Range_Type.range -> 'a withinfo_t =
  fun v -> fun r -> { v; p = r }
let withsort : 'a . 'a -> 'a withinfo_t =
  fun v -> withinfo v FStarC_Compiler_Range_Type.dummyRange
let (order_bv : bv -> bv -> Prims.int) = fun x -> fun y -> x.index - y.index
let (bv_eq : bv -> bv -> Prims.bool) =
  fun x -> fun y -> let uu___ = order_bv x y in uu___ = Prims.int_zero
let (order_ident : FStarC_Ident.ident -> FStarC_Ident.ident -> Prims.int) =
  fun x ->
    fun y ->
      let uu___ = FStarC_Ident.string_of_id x in
      let uu___1 = FStarC_Ident.string_of_id y in
      FStarC_Compiler_String.compare uu___ uu___1
let (order_fv : FStarC_Ident.lident -> FStarC_Ident.lident -> Prims.int) =
  fun x ->
    fun y ->
      let uu___ = FStarC_Ident.string_of_lid x in
      let uu___1 = FStarC_Ident.string_of_lid y in
      FStarC_Compiler_String.compare uu___ uu___1
let (range_of_lbname : lbname -> FStarC_Compiler_Range_Type.range) =
  fun l ->
    match l with
    | FStar_Pervasives.Inl x -> FStarC_Ident.range_of_id x.ppname
    | FStar_Pervasives.Inr fv1 -> FStarC_Ident.range_of_lid (fv1.fv_name).v
let (range_of_bv : bv -> FStarC_Compiler_Range_Type.range) =
  fun x -> FStarC_Ident.range_of_id x.ppname
let (set_range_of_bv : bv -> FStarC_Compiler_Range_Type.range -> bv) =
  fun x ->
    fun r ->
      let uu___ = FStarC_Ident.set_id_range r x.ppname in
      { ppname = uu___; index = (x.index); sort = (x.sort) }
let (on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo) =
  fun f ->
    fun qi ->
      let uu___ = qi.antiquotations in
      match uu___ with
      | (s, aqs) ->
          let aqs' = FStarC_Compiler_List.map f aqs in
          { qkind = (qi.qkind); antiquotations = (s, aqs') }
let (lookup_aq : bv -> antiquotations -> term) =
  fun bv1 ->
    fun aq ->
      try
        (fun uu___ ->
           match () with
           | () ->
               FStarC_Compiler_List.nth (FStar_Pervasives_Native.snd aq)
                 ((((FStarC_Compiler_List.length
                       (FStar_Pervasives_Native.snd aq))
                      - Prims.int_one)
                     - bv1.index)
                    + (FStar_Pervasives_Native.fst aq))) ()
      with | uu___ -> failwith "antiquotation out of bounds"
type path = Prims.string Prims.list
type subst_t = subst_elt Prims.list
let deq_instance_from_cmp :
  'uuuuu .
    ('uuuuu -> 'uuuuu -> FStarC_Compiler_Order.order) ->
      'uuuuu FStarC_Class_Deq.deq
  =
  fun f ->
    {
      FStarC_Class_Deq.op_Equals_Question =
        (fun x ->
           fun y -> let uu___ = f x y in FStarC_Compiler_Order.eq uu___)
    }
let ord_instance_from_cmp :
  'uuuuu .
    ('uuuuu -> 'uuuuu -> FStarC_Compiler_Order.order) ->
      'uuuuu FStarC_Class_Ord.ord
  =
  fun f ->
    {
      FStarC_Class_Ord.super = (deq_instance_from_cmp f);
      FStarC_Class_Ord.cmp = f
    }
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x ->
    fun y ->
      let uu___ = FStarC_Ident.string_of_id x in
      let uu___1 = FStarC_Ident.string_of_id y in
      FStarC_Compiler_String.compare uu___ uu___1
let (deq_bv : bv FStarC_Class_Deq.deq) =
  deq_instance_from_cmp
    (fun x ->
       fun y ->
         let uu___ = order_bv x y in
         FStarC_Compiler_Order.order_from_int uu___)
let (deq_ident : FStarC_Ident.ident FStarC_Class_Deq.deq) =
  deq_instance_from_cmp
    (fun x ->
       fun y ->
         let uu___ = order_ident x y in
         FStarC_Compiler_Order.order_from_int uu___)
let (deq_fv : FStarC_Ident.lident FStarC_Class_Deq.deq) =
  deq_instance_from_cmp
    (fun x ->
       fun y ->
         let uu___ = order_fv x y in
         FStarC_Compiler_Order.order_from_int uu___)
let (deq_univ_name : univ_name FStarC_Class_Deq.deq) =
  deq_instance_from_cmp
    (fun x ->
       fun y ->
         let uu___ = order_univ_name x y in
         FStarC_Compiler_Order.order_from_int uu___)
let (deq_delta_depth : delta_depth FStarC_Class_Deq.deq) =
  { FStarC_Class_Deq.op_Equals_Question = (fun x -> fun y -> x = y) }
let (ord_bv : bv FStarC_Class_Ord.ord) =
  ord_instance_from_cmp
    (fun x ->
       fun y ->
         let uu___ = order_bv x y in
         FStarC_Compiler_Order.order_from_int uu___)
let (ord_ident : FStarC_Ident.ident FStarC_Class_Ord.ord) =
  ord_instance_from_cmp
    (fun x ->
       fun y ->
         let uu___ = order_ident x y in
         FStarC_Compiler_Order.order_from_int uu___)
let (ord_fv : FStarC_Ident.lident FStarC_Class_Ord.ord) =
  ord_instance_from_cmp
    (fun x ->
       fun y ->
         let uu___ = order_fv x y in
         FStarC_Compiler_Order.order_from_int uu___)
let syn :
  'uuuuu 'uuuuu1 'uuuuu2 .
    'uuuuu -> 'uuuuu1 -> ('uuuuu1 -> 'uuuuu -> 'uuuuu2) -> 'uuuuu2
  = fun p -> fun k -> fun f -> f k p
let mk_fvs :
  'uuuuu .
    unit -> 'uuuuu FStar_Pervasives_Native.option FStarC_Compiler_Effect.ref
  = fun uu___ -> FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let mk_uvs :
  'uuuuu .
    unit -> 'uuuuu FStar_Pervasives_Native.option FStarC_Compiler_Effect.ref
  = fun uu___ -> FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (list_of_freenames : freenames -> bv Prims.list) =
  fun fvs ->
    FStarC_Class_Setlike.elems ()
      (Obj.magic (FStarC_Compiler_FlatSet.setlike_flat_set ord_bv))
      (Obj.magic fvs)
let mk : 'a . 'a -> FStarC_Compiler_Range_Type.range -> 'a syntax =
  fun t ->
    fun r ->
      let uu___ = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
      let uu___1 = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
      { n = t; pos = r; vars = uu___; hash_code = uu___1 }
let (bv_to_tm : bv -> term) =
  fun bv1 -> let uu___ = range_of_bv bv1 in mk (Tm_bvar bv1) uu___
let (bv_to_name : bv -> term) =
  fun bv1 -> let uu___ = range_of_bv bv1 in mk (Tm_name bv1) uu___
let (binders_to_names : binders -> term Prims.list) =
  fun bs -> FStarC_Compiler_List.map (fun b -> bv_to_name b.binder_bv) bs
let (mk_Tm_app : term -> args -> FStarC_Compiler_Range_Type.range -> term) =
  fun t1 ->
    fun args1 ->
      fun p ->
        match args1 with
        | [] -> t1
        | uu___ -> mk (Tm_app { hd = t1; args = args1 }) p
let (mk_Tm_uinst : term -> universes -> term) =
  fun t ->
    fun us ->
      match t.n with
      | Tm_fvar uu___ ->
          (match us with | [] -> t | us1 -> mk (Tm_uinst (t, us1)) t.pos)
      | uu___ -> failwith "Unexpected universe instantiation"
let (extend_app_n : term -> args -> FStarC_Compiler_Range_Type.range -> term)
  =
  fun t ->
    fun args' ->
      fun r ->
        match t.n with
        | Tm_app { hd; args = args1;_} ->
            mk_Tm_app hd (FStarC_Compiler_List.op_At args1 args') r
        | uu___ -> mk_Tm_app t args' r
let (extend_app : term -> arg -> FStarC_Compiler_Range_Type.range -> term) =
  fun t -> fun arg1 -> fun r -> extend_app_n t [arg1] r
let (mk_Tm_delayed :
  (term * subst_ts) -> FStarC_Compiler_Range_Type.range -> term) =
  fun lr ->
    fun pos ->
      mk
        (Tm_delayed
           {
             tm1 = (FStar_Pervasives_Native.fst lr);
             substs = (FStar_Pervasives_Native.snd lr)
           }) pos
let (mk_Total : typ -> comp) = fun t -> mk (Total t) t.pos
let (mk_GTotal : typ -> comp) = fun t -> mk (GTotal t) t.pos
let (mk_Comp : comp_typ -> comp) = fun ct -> mk (Comp ct) (ct.result_typ).pos
let (mk_lb :
  (lbname * univ_name Prims.list * FStarC_Ident.lident * typ * term *
    attribute Prims.list * FStarC_Compiler_Range_Type.range) -> letbinding)
  =
  fun uu___ ->
    match uu___ with
    | (x, univs, eff, t, e, attrs, pos) ->
        {
          lbname = x;
          lbunivs = univs;
          lbtyp = t;
          lbeff = eff;
          lbdef = e;
          lbattrs = attrs;
          lbpos = pos
        }
let (mk_Tac : typ -> comp) =
  fun t ->
    mk_Comp
      {
        comp_univs = [U_zero];
        effect_name = FStarC_Parser_Const.effect_Tac_lid;
        result_typ = t;
        effect_args = [];
        flags = [SOMETRIVIAL; TRIVIAL_POSTCONDITION]
      }
let (default_sigmeta : sig_metadata) =
  {
    sigmeta_active = true;
    sigmeta_fact_db_ids = [];
    sigmeta_admit = false;
    sigmeta_spliced = false;
    sigmeta_already_checked = false;
    sigmeta_extension_data = []
  }
let (mk_sigelt : sigelt' -> sigelt) =
  fun e ->
    {
      sigel = e;
      sigrng = FStarC_Compiler_Range_Type.dummyRange;
      sigquals = [];
      sigmeta = default_sigmeta;
      sigattrs = [];
      sigopens_and_abbrevs = [];
      sigopts = FStar_Pervasives_Native.None
    }
let (mk_subst : subst_t -> subst_t) = fun s -> s
let (extend_subst : subst_elt -> subst_elt Prims.list -> subst_t) =
  fun x -> fun s -> x :: s
let (argpos : arg -> FStarC_Compiler_Range_Type.range) =
  fun x -> (FStar_Pervasives_Native.fst x).pos
let (tun : term) = mk Tm_unknown FStarC_Compiler_Range_Type.dummyRange
let (teff : term) =
  mk (Tm_constant FStarC_Const.Const_effect)
    FStarC_Compiler_Range_Type.dummyRange
let (is_teff : term -> Prims.bool) =
  fun t ->
    match t.n with
    | Tm_constant (FStarC_Const.Const_effect) -> true
    | uu___ -> false
let (is_type : term -> Prims.bool) =
  fun t -> match t.n with | Tm_type uu___ -> true | uu___ -> false
let (null_id : FStarC_Ident.ident) =
  FStarC_Ident.mk_ident ("_", FStarC_Compiler_Range_Type.dummyRange)
let (null_bv : term -> bv) =
  fun k ->
    let uu___ = FStarC_GenSym.next_id () in
    { ppname = null_id; index = uu___; sort = k }
let (is_null_bv : bv -> Prims.bool) =
  fun b ->
    let uu___ = FStarC_Ident.string_of_id b.ppname in
    let uu___1 = FStarC_Ident.string_of_id null_id in uu___ = uu___1
let (is_null_binder : binder -> Prims.bool) = fun b -> is_null_bv b.binder_bv
let (range_of_ropt :
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
    FStarC_Compiler_Range_Type.range)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStarC_Compiler_Range_Type.dummyRange
    | FStar_Pervasives_Native.Some r -> r
let (gen_bv' :
  FStarC_Ident.ident ->
    FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
      typ -> bv)
  =
  fun id ->
    fun r ->
      fun t ->
        let uu___ = FStarC_GenSym.next_id () in
        { ppname = id; index = uu___; sort = t }
let (gen_bv :
  Prims.string ->
    FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
      typ -> bv)
  =
  fun s ->
    fun r ->
      fun t ->
        let id = FStarC_Ident.mk_ident (s, (range_of_ropt r)) in
        gen_bv' id r t
let (new_bv :
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
    typ -> bv)
  = fun ropt -> fun t -> gen_bv FStarC_Ident.reserved_prefix ropt t
let (freshen_bv : bv -> bv) =
  fun bv1 ->
    let uu___ = is_null_bv bv1 in
    if uu___
    then
      let uu___1 =
        let uu___2 = range_of_bv bv1 in FStar_Pervasives_Native.Some uu___2 in
      new_bv uu___1 bv1.sort
    else
      (let uu___2 = FStarC_GenSym.next_id () in
       { ppname = (bv1.ppname); index = uu___2; sort = (bv1.sort) })
let (mk_binder_with_attrs :
  bv ->
    bqual ->
      positivity_qualifier FStar_Pervasives_Native.option ->
        attribute Prims.list -> binder)
  =
  fun bv1 ->
    fun aqual1 ->
      fun pqual ->
        fun attrs ->
          {
            binder_bv = bv1;
            binder_qual = aqual1;
            binder_positivity = pqual;
            binder_attrs = attrs
          }
let (mk_binder : bv -> binder) =
  fun a ->
    mk_binder_with_attrs a FStar_Pervasives_Native.None
      FStar_Pervasives_Native.None []
let (null_binder : term -> binder) =
  fun t -> let uu___ = null_bv t in mk_binder uu___
let (imp_tag : binder_qualifier) = Implicit false
let (iarg : term -> arg) =
  fun t ->
    (t,
      (FStar_Pervasives_Native.Some
         { aqual_implicit = true; aqual_attributes = [] }))
let (as_arg : term -> arg) = fun t -> (t, FStar_Pervasives_Native.None)
let (is_top_level : letbinding Prims.list -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | { lbname = FStar_Pervasives.Inr uu___1; lbunivs = uu___2;
        lbtyp = uu___3; lbeff = uu___4; lbdef = uu___5; lbattrs = uu___6;
        lbpos = uu___7;_}::uu___8 -> true
    | uu___1 -> false
let (freenames_of_binders : binders -> freenames) =
  fun bs ->
    let uu___ =
      Obj.magic
        (FStarC_Class_Setlike.empty ()
           (Obj.magic (FStarC_Compiler_FlatSet.setlike_flat_set ord_bv)) ()) in
    FStarC_Compiler_List.fold_right
      (fun uu___2 ->
         fun uu___1 ->
           (fun b ->
              fun out ->
                Obj.magic
                  (FStarC_Class_Setlike.add ()
                     (Obj.magic
                        (FStarC_Compiler_FlatSet.setlike_flat_set ord_bv))
                     b.binder_bv (Obj.magic out))) uu___2 uu___1) bs uu___
let (binders_of_list : bv Prims.list -> binders) =
  fun fvs -> FStarC_Compiler_List.map (fun t -> mk_binder t) fvs
let (binders_of_freenames : freenames -> binders) =
  fun fvs ->
    let uu___ =
      FStarC_Class_Setlike.elems ()
        (Obj.magic (FStarC_Compiler_FlatSet.setlike_flat_set ord_bv))
        (Obj.magic fvs) in
    binders_of_list uu___
let (is_bqual_implicit : bqual -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some (Implicit uu___1) -> true
    | uu___1 -> false
let (is_aqual_implicit : aqual -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some
        { aqual_implicit = b; aqual_attributes = uu___1;_} -> b
    | uu___1 -> false
let (is_bqual_implicit_or_meta : bqual -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some (Implicit uu___1) -> true
    | FStar_Pervasives_Native.Some (Meta uu___1) -> true
    | uu___1 -> false
let (as_bqual_implicit : Prims.bool -> bqual) =
  fun uu___ ->
    if uu___
    then FStar_Pervasives_Native.Some imp_tag
    else FStar_Pervasives_Native.None
let (as_aqual_implicit : Prims.bool -> aqual) =
  fun uu___ ->
    if uu___
    then
      FStar_Pervasives_Native.Some
        { aqual_implicit = true; aqual_attributes = [] }
    else FStar_Pervasives_Native.None
let (pat_bvs : pat -> bv Prims.list) =
  fun p ->
    let rec aux b p1 =
      match p1.v with
      | Pat_dot_term uu___ -> b
      | Pat_constant uu___ -> b
      | Pat_var x -> x :: b
      | Pat_cons (uu___, uu___1, pats) ->
          FStarC_Compiler_List.fold_left
            (fun b1 ->
               fun uu___2 -> match uu___2 with | (p2, uu___3) -> aux b1 p2) b
            pats in
    let uu___ = aux [] p in FStarC_Compiler_List.rev uu___
let (freshen_binder : binder -> binder) =
  fun b ->
    let uu___ = freshen_bv b.binder_bv in
    {
      binder_bv = uu___;
      binder_qual = (b.binder_qual);
      binder_positivity = (b.binder_positivity);
      binder_attrs = (b.binder_attrs)
    }
let (new_univ_name :
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
    univ_name)
  =
  fun ropt ->
    let id = FStarC_GenSym.next_id () in
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Compiler_Util.string_of_int id in
        Prims.strcat FStarC_Ident.reserved_prefix uu___2 in
      (uu___1, (range_of_ropt ropt)) in
    FStarC_Ident.mk_ident uu___
let (lbname_eq :
  (bv, FStarC_Ident.lident) FStar_Pervasives.either ->
    (bv, FStarC_Ident.lident) FStar_Pervasives.either -> Prims.bool)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (FStar_Pervasives.Inl x, FStar_Pervasives.Inl y) -> bv_eq x y
      | (FStar_Pervasives.Inr l, FStar_Pervasives.Inr m) ->
          FStarC_Ident.lid_equals l m
      | uu___ -> false
let (fv_eq : fv -> fv -> Prims.bool) =
  fun fv1 ->
    fun fv2 -> FStarC_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
let (fv_eq_lid : fv -> FStarC_Ident.lident -> Prims.bool) =
  fun fv1 -> fun lid -> FStarC_Ident.lid_equals (fv1.fv_name).v lid
let (set_bv_range : bv -> FStarC_Compiler_Range_Type.range -> bv) =
  fun bv1 ->
    fun r ->
      let uu___ = FStarC_Ident.set_id_range r bv1.ppname in
      { ppname = uu___; index = (bv1.index); sort = (bv1.sort) }
let (lid_and_dd_as_fv :
  FStarC_Ident.lident -> fv_qual FStar_Pervasives_Native.option -> fv) =
  fun l ->
    fun dq ->
      let uu___ =
        let uu___1 = FStarC_Ident.range_of_lid l in withinfo l uu___1 in
      { fv_name = uu___; fv_qual = dq }
let (lid_as_fv :
  FStarC_Ident.lident -> fv_qual FStar_Pervasives_Native.option -> fv) =
  fun l ->
    fun dq ->
      let uu___ =
        let uu___1 = FStarC_Ident.range_of_lid l in withinfo l uu___1 in
      { fv_name = uu___; fv_qual = dq }
let (fv_to_tm : fv -> term) =
  fun fv1 ->
    let uu___ = FStarC_Ident.range_of_lid (fv1.fv_name).v in
    mk (Tm_fvar fv1) uu___
let (fvar_with_dd :
  FStarC_Ident.lident -> fv_qual FStar_Pervasives_Native.option -> term) =
  fun l -> fun dq -> let uu___ = lid_and_dd_as_fv l dq in fv_to_tm uu___
let (fvar :
  FStarC_Ident.lident -> fv_qual FStar_Pervasives_Native.option -> term) =
  fun l -> fun dq -> let uu___ = lid_as_fv l dq in fv_to_tm uu___
let (lid_of_fv : fv -> FStarC_Ident.lid) = fun fv1 -> (fv1.fv_name).v
let (range_of_fv : fv -> FStarC_Compiler_Range_Type.range) =
  fun fv1 -> let uu___ = lid_of_fv fv1 in FStarC_Ident.range_of_lid uu___
let (set_range_of_fv : fv -> FStarC_Compiler_Range_Type.range -> fv) =
  fun fv1 ->
    fun r ->
      let uu___ =
        let uu___1 = fv1.fv_name in
        let uu___2 =
          let uu___3 = lid_of_fv fv1 in FStarC_Ident.set_lid_range uu___3 r in
        { v = uu___2; p = (uu___1.p) } in
      { fv_name = uu___; fv_qual = (fv1.fv_qual) }
let (has_simple_attribute : term Prims.list -> Prims.string -> Prims.bool) =
  fun l ->
    fun s ->
      FStarC_Compiler_List.existsb
        (fun uu___ ->
           match uu___ with
           | { n = Tm_constant (FStarC_Const.Const_string (data, uu___1));
               pos = uu___2; vars = uu___3; hash_code = uu___4;_} when
               data = s -> true
           | uu___1 -> false) l
let rec (eq_pat : pat -> pat -> Prims.bool) =
  fun p1 ->
    fun p2 ->
      match ((p1.v), (p2.v)) with
      | (Pat_constant c1, Pat_constant c2) -> FStarC_Const.eq_const c1 c2
      | (Pat_cons (fv1, us1, as1), Pat_cons (fv2, us2, as2)) ->
          let uu___ =
            (fv_eq fv1 fv2) &&
              ((FStarC_Compiler_List.length as1) =
                 (FStarC_Compiler_List.length as2)) in
          if uu___
          then
            (FStarC_Compiler_List.forall2
               (fun uu___1 ->
                  fun uu___2 ->
                    match (uu___1, uu___2) with
                    | ((p11, b1), (p21, b2)) -> (b1 = b2) && (eq_pat p11 p21))
               as1 as2)
              &&
              ((match (us1, us2) with
                | (FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None) -> true
                | (FStar_Pervasives_Native.Some us11,
                   FStar_Pervasives_Native.Some us21) ->
                    (FStarC_Compiler_List.length us11) =
                      (FStarC_Compiler_List.length us21)
                | uu___1 -> false))
          else false
      | (Pat_var uu___, Pat_var uu___1) -> true
      | (Pat_dot_term uu___, Pat_dot_term uu___1) -> true
      | (uu___, uu___1) -> false
let (delta_constant : delta_depth) = Delta_constant_at_level Prims.int_zero
let (delta_equational : delta_depth) =
  Delta_equational_at_level Prims.int_zero
let (fvconst : FStarC_Ident.lident -> fv) =
  fun l -> lid_and_dd_as_fv l FStar_Pervasives_Native.None
let (tconst : FStarC_Ident.lident -> term) =
  fun l ->
    let uu___ = let uu___1 = fvconst l in Tm_fvar uu___1 in
    mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (tabbrev : FStarC_Ident.lident -> term) =
  fun l ->
    let uu___ =
      let uu___1 = lid_and_dd_as_fv l FStar_Pervasives_Native.None in
      Tm_fvar uu___1 in
    mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (tdataconstr : FStarC_Ident.lident -> term) =
  fun l ->
    let uu___ = lid_and_dd_as_fv l (FStar_Pervasives_Native.Some Data_ctor) in
    fv_to_tm uu___
let (t_unit : term) = tconst FStarC_Parser_Const.unit_lid
let (t_bool : term) = tconst FStarC_Parser_Const.bool_lid
let (t_int : term) = tconst FStarC_Parser_Const.int_lid
let (t_string : term) = tconst FStarC_Parser_Const.string_lid
let (t_exn : term) = tconst FStarC_Parser_Const.exn_lid
let (t_real : term) = tconst FStarC_Parser_Const.real_lid
let (t_float : term) = tconst FStarC_Parser_Const.float_lid
let (t_char : term) = tabbrev FStarC_Parser_Const.char_lid
let (t_range : term) = tconst FStarC_Parser_Const.range_lid
let (t___range : term) = tconst FStarC_Parser_Const.__range_lid
let (t_vconfig : term) = tconst FStarC_Parser_Const.vconfig_lid
let (t_term : term) = tconst FStarC_Parser_Const.term_lid
let (t_term_view : term) = tabbrev FStarC_Parser_Const.term_view_lid
let (t_order : term) = tconst FStarC_Parser_Const.order_lid
let (t_decls : term) = tabbrev FStarC_Parser_Const.decls_lid
let (t_binder : term) = tconst FStarC_Parser_Const.binder_lid
let (t_binders : term) = tconst FStarC_Parser_Const.binders_lid
let (t_bv : term) = tconst FStarC_Parser_Const.bv_lid
let (t_fv : term) = tconst FStarC_Parser_Const.fv_lid
let (t_norm_step : term) = tconst FStarC_Parser_Const.norm_step_lid
let (t_tac_of : term -> term -> term) =
  fun a ->
    fun b ->
      let uu___ =
        let uu___1 = tabbrev FStarC_Parser_Const.tac_lid in
        mk_Tm_uinst uu___1 [U_zero; U_zero] in
      let uu___1 =
        let uu___2 = as_arg a in
        let uu___3 = let uu___4 = as_arg b in [uu___4] in uu___2 :: uu___3 in
      mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_tactic_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStarC_Parser_Const.tactic_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_tactic_unit : term) = t_tactic_of t_unit
let (t_list_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStarC_Parser_Const.list_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_option_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStarC_Parser_Const.option_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_tuple2_of : term -> term -> term) =
  fun t1 ->
    fun t2 ->
      let uu___ =
        let uu___1 = tabbrev FStarC_Parser_Const.lid_tuple2 in
        mk_Tm_uinst uu___1 [U_zero; U_zero] in
      let uu___1 =
        let uu___2 = as_arg t1 in
        let uu___3 = let uu___4 = as_arg t2 in [uu___4] in uu___2 :: uu___3 in
      mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_tuple3_of : term -> term -> term -> term) =
  fun t1 ->
    fun t2 ->
      fun t3 ->
        let uu___ =
          let uu___1 = tabbrev FStarC_Parser_Const.lid_tuple3 in
          mk_Tm_uinst uu___1 [U_zero; U_zero; U_zero] in
        let uu___1 =
          let uu___2 = as_arg t1 in
          let uu___3 =
            let uu___4 = as_arg t2 in
            let uu___5 = let uu___6 = as_arg t3 in [uu___6] in uu___4 ::
              uu___5 in
          uu___2 :: uu___3 in
        mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_tuple4_of : term -> term -> term -> term -> term) =
  fun t1 ->
    fun t2 ->
      fun t3 ->
        fun t4 ->
          let uu___ =
            let uu___1 = tabbrev FStarC_Parser_Const.lid_tuple4 in
            mk_Tm_uinst uu___1 [U_zero; U_zero; U_zero; U_zero] in
          let uu___1 =
            let uu___2 = as_arg t1 in
            let uu___3 =
              let uu___4 = as_arg t2 in
              let uu___5 =
                let uu___6 = as_arg t3 in
                let uu___7 = let uu___8 = as_arg t4 in [uu___8] in uu___6 ::
                  uu___7 in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_tuple5_of : term -> term -> term -> term -> term -> term) =
  fun t1 ->
    fun t2 ->
      fun t3 ->
        fun t4 ->
          fun t5 ->
            let uu___ =
              let uu___1 = tabbrev FStarC_Parser_Const.lid_tuple5 in
              mk_Tm_uinst uu___1 [U_zero; U_zero; U_zero; U_zero; U_zero] in
            let uu___1 =
              let uu___2 = as_arg t1 in
              let uu___3 =
                let uu___4 = as_arg t2 in
                let uu___5 =
                  let uu___6 = as_arg t3 in
                  let uu___7 =
                    let uu___8 = as_arg t4 in
                    let uu___9 = let uu___10 = as_arg t5 in [uu___10] in
                    uu___8 :: uu___9 in
                  uu___6 :: uu___7 in
                uu___4 :: uu___5 in
              uu___2 :: uu___3 in
            mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_either_of : term -> term -> term) =
  fun t1 ->
    fun t2 ->
      let uu___ =
        let uu___1 = tabbrev FStarC_Parser_Const.either_lid in
        mk_Tm_uinst uu___1 [U_zero; U_zero] in
      let uu___1 =
        let uu___2 = as_arg t1 in
        let uu___3 = let uu___4 = as_arg t2 in [uu___4] in uu___2 :: uu___3 in
      mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_sealed_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStarC_Parser_Const.sealed_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (t_erased_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStarC_Parser_Const.erased_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStarC_Compiler_Range_Type.dummyRange
let (unit_const_with_range : FStarC_Compiler_Range_Type.range -> term) =
  fun r -> mk (Tm_constant FStarC_Const.Const_unit) r
let (unit_const : term) =
  unit_const_with_range FStarC_Compiler_Range_Type.dummyRange
let (show_restriction : restriction FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Unrestricted -> "Unrestricted"
         | AllowList allow_list ->
             let uu___1 =
               let uu___2 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_list
                      (FStarC_Class_Show.show_tuple2
                         FStarC_Ident.showable_ident
                         (FStarC_Class_Show.show_option
                            FStarC_Ident.showable_ident))) allow_list in
               Prims.strcat uu___2 ")" in
             Prims.strcat "(AllowList " uu___1)
  }
let (is_ident_allowed_by_restriction' :
  FStarC_Ident.ident ->
    restriction -> FStarC_Ident.ident FStar_Pervasives_Native.option)
  =
  fun id ->
    fun uu___ ->
      match uu___ with
      | Unrestricted -> FStar_Pervasives_Native.Some id
      | AllowList allow_list ->
          let uu___1 =
            FStarC_Compiler_List.find
              (fun uu___2 ->
                 match uu___2 with
                 | (dest_id, renamed_id) ->
                     FStarC_Class_Deq.op_Equals_Question deq_univ_name
                       (FStarC_Compiler_Util.dflt dest_id renamed_id) id)
              allow_list in
          FStarC_Compiler_Util.map_opt uu___1 FStar_Pervasives_Native.fst
let (is_ident_allowed_by_restriction :
  FStarC_Ident.ident ->
    restriction -> FStarC_Ident.ident FStar_Pervasives_Native.option)
  =
  let debug = FStarC_Compiler_Debug.get_toggle "open_include_restrictions" in
  fun id ->
    fun restriction1 ->
      let result = is_ident_allowed_by_restriction' id restriction1 in
      (let uu___1 = FStarC_Compiler_Effect.op_Bang debug in
       if uu___1
       then
         let uu___2 =
           let uu___3 =
             let uu___4 =
               FStarC_Class_Show.show FStarC_Ident.showable_ident id in
             let uu___5 =
               let uu___6 =
                 let uu___7 =
                   FStarC_Class_Show.show show_restriction restriction1 in
                 let uu___8 =
                   let uu___9 =
                     FStarC_Class_Show.show
                       (FStarC_Class_Show.show_option
                          FStarC_Ident.showable_ident) result in
                   Prims.strcat ") = " uu___9 in
                 Prims.strcat uu___7 uu___8 in
               Prims.strcat ", " uu___6 in
             Prims.strcat uu___4 uu___5 in
           Prims.strcat "is_ident_allowed_by_restriction(" uu___3 in
         FStarC_Compiler_Util.print_endline uu___2
       else ());
      result
let has_range_syntax : 'a . unit -> 'a syntax FStarC_Class_HasRange.hasRange
  =
  fun uu___ ->
    {
      FStarC_Class_HasRange.pos = (fun t -> t.pos);
      FStarC_Class_HasRange.setPos =
        (fun r ->
           fun t ->
             { n = (t.n); pos = r; vars = (t.vars); hash_code = (t.hash_code)
             })
    }
let has_range_withinfo :
  'a . unit -> 'a withinfo_t FStarC_Class_HasRange.hasRange =
  fun uu___ ->
    {
      FStarC_Class_HasRange.pos = (fun t -> t.p);
      FStarC_Class_HasRange.setPos = (fun r -> fun t -> { v = (t.v); p = r })
    }
let (has_range_sigelt : sigelt FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = (fun t -> t.sigrng);
    FStarC_Class_HasRange.setPos =
      (fun r ->
         fun t ->
           {
             sigel = (t.sigel);
             sigrng = r;
             sigquals = (t.sigquals);
             sigmeta = (t.sigmeta);
             sigattrs = (t.sigattrs);
             sigopens_and_abbrevs = (t.sigopens_and_abbrevs);
             sigopts = (t.sigopts)
           })
  }
let (hasRange_fv : fv FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = range_of_fv;
    FStarC_Class_HasRange.setPos = (fun r -> fun f -> set_range_of_fv f r)
  }
let (hasRange_bv : bv FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = range_of_bv;
    FStarC_Class_HasRange.setPos = (fun r -> fun f -> set_range_of_bv f r)
  }
let (hasRange_binder : binder FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos =
      (fun b -> FStarC_Class_HasRange.pos hasRange_bv b.binder_bv);
    FStarC_Class_HasRange.setPos =
      (fun r ->
         fun b ->
           let uu___ = FStarC_Class_HasRange.setPos hasRange_bv r b.binder_bv in
           {
             binder_bv = uu___;
             binder_qual = (b.binder_qual);
             binder_positivity = (b.binder_positivity);
             binder_attrs = (b.binder_attrs)
           })
  }
let (showable_lazy_kind : lazy_kind FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | BadLazy -> "BadLazy"
         | Lazy_bv -> "Lazy_bv"
         | Lazy_namedv -> "Lazy_namedv"
         | Lazy_binder -> "Lazy_binder"
         | Lazy_optionstate -> "Lazy_optionstate"
         | Lazy_fvar -> "Lazy_fvar"
         | Lazy_comp -> "Lazy_comp"
         | Lazy_env -> "Lazy_env"
         | Lazy_proofstate -> "Lazy_proofstate"
         | Lazy_goal -> "Lazy_goal"
         | Lazy_sigelt -> "Lazy_sigelt"
         | Lazy_letbinding -> "Lazy_letbinding"
         | Lazy_uvar -> "Lazy_uvar"
         | Lazy_universe -> "Lazy_universe"
         | Lazy_universe_uvar -> "Lazy_universe_uvar"
         | Lazy_issue -> "Lazy_issue"
         | Lazy_doc -> "Lazy_doc"
         | Lazy_ident -> "Lazy_ident"
         | Lazy_tref -> "Lazy_tref"
         | Lazy_embedding uu___1 -> "Lazy_embedding _"
         | Lazy_extension s -> Prims.strcat "Lazy_extension " s
         | uu___1 -> failwith "FIXME! lazy_kind_to_string must be complete")
  }
let (showable_restriction : restriction FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Unrestricted -> "Unrestricted"
         | AllowList l ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    (FStarC_Class_Show.show_tuple2
                       FStarC_Ident.showable_ident
                       (FStarC_Class_Show.show_option
                          FStarC_Ident.showable_ident))) l in
             Prims.strcat "AllowList " uu___1)
  }
let (deq_lazy_kind : lazy_kind FStarC_Class_Deq.deq) =
  {
    FStarC_Class_Deq.op_Equals_Question =
      (fun k ->
         fun k' ->
           match (k, k') with
           | (BadLazy, BadLazy) -> true
           | (Lazy_bv, Lazy_bv) -> true
           | (Lazy_namedv, Lazy_namedv) -> true
           | (Lazy_binder, Lazy_binder) -> true
           | (Lazy_optionstate, Lazy_optionstate) -> true
           | (Lazy_fvar, Lazy_fvar) -> true
           | (Lazy_comp, Lazy_comp) -> true
           | (Lazy_env, Lazy_env) -> true
           | (Lazy_proofstate, Lazy_proofstate) -> true
           | (Lazy_goal, Lazy_goal) -> true
           | (Lazy_sigelt, Lazy_sigelt) -> true
           | (Lazy_letbinding, Lazy_letbinding) -> true
           | (Lazy_uvar, Lazy_uvar) -> true
           | (Lazy_universe, Lazy_universe) -> true
           | (Lazy_universe_uvar, Lazy_universe_uvar) -> true
           | (Lazy_issue, Lazy_issue) -> true
           | (Lazy_ident, Lazy_ident) -> true
           | (Lazy_doc, Lazy_doc) -> true
           | (Lazy_tref, Lazy_tref) -> true
           | (Lazy_extension s, Lazy_extension t) -> s = t
           | (Lazy_embedding uu___, uu___1) -> false
           | (uu___, Lazy_embedding uu___1) -> false
           | uu___ -> false)
  }
let (tagged_term : term FStarC_Class_Tagged.tagged) =
  {
    FStarC_Class_Tagged.tag_of =
      (fun t ->
         match t.n with
         | Tm_bvar { ppname = uu___; index = uu___1; sort = uu___2;_} ->
             "Tm_bvar"
         | Tm_name { ppname = uu___; index = uu___1; sort = uu___2;_} ->
             "Tm_name"
         | Tm_fvar { fv_name = uu___; fv_qual = uu___1;_} -> "Tm_fvar"
         | Tm_uinst (uu___, uu___1) -> "Tm_uinst"
         | Tm_constant uu___ -> "Tm_constant"
         | Tm_type uu___ -> "Tm_type"
         | Tm_quoted
             (uu___, { qkind = Quote_static; antiquotations = uu___1;_}) ->
             "Tm_quoted(static)"
         | Tm_quoted
             (uu___, { qkind = Quote_dynamic; antiquotations = uu___1;_}) ->
             "Tm_quoted(dynamic)"
         | Tm_abs { bs = uu___; body = uu___1; rc_opt = uu___2;_} -> "Tm_abs"
         | Tm_arrow { bs1 = uu___; comp = uu___1;_} -> "Tm_arrow"
         | Tm_refine { b = uu___; phi = uu___1;_} -> "Tm_refine"
         | Tm_app { hd = uu___; args = uu___1;_} -> "Tm_app"
         | Tm_match
             { scrutinee = uu___; ret_opt = uu___1; brs = uu___2;
               rc_opt1 = uu___3;_}
             -> "Tm_match"
         | Tm_ascribed { tm = uu___; asc = uu___1; eff_opt = uu___2;_} ->
             "Tm_ascribed"
         | Tm_let { lbs = uu___; body1 = uu___1;_} -> "Tm_let"
         | Tm_uvar (uu___, uu___1) -> "Tm_uvar"
         | Tm_delayed { tm1 = uu___; substs = uu___1;_} -> "Tm_delayed"
         | Tm_meta { tm2 = uu___; meta = uu___1;_} -> "Tm_meta"
         | Tm_unknown -> "Tm_unknown"
         | Tm_lazy
             { blob = uu___; lkind = uu___1; ltyp = uu___2; rng = uu___3;_}
             -> "Tm_lazy")
  }
let (tagged_sigelt : sigelt FStarC_Class_Tagged.tagged) =
  {
    FStarC_Class_Tagged.tag_of =
      (fun se ->
         match se.sigel with
         | Sig_inductive_typ
             { lid = uu___; us = uu___1; params = uu___2;
               num_uniform_params = uu___3; t = uu___4; mutuals = uu___5;
               ds = uu___6; injective_type_params = uu___7;_}
             -> "Sig_inductive_typ"
         | Sig_bundle { ses = uu___; lids = uu___1;_} -> "Sig_bundle"
         | Sig_datacon
             { lid1 = uu___; us1 = uu___1; t1 = uu___2; ty_lid = uu___3;
               num_ty_params = uu___4; mutuals1 = uu___5;
               injective_type_params1 = uu___6;_}
             -> "Sig_datacon"
         | Sig_declare_typ { lid2 = uu___; us2 = uu___1; t2 = uu___2;_} ->
             "Sig_declare_typ"
         | Sig_let { lbs1 = uu___; lids1 = uu___1;_} -> "Sig_let"
         | Sig_assume { lid3 = uu___; us3 = uu___1; phi1 = uu___2;_} ->
             "Sig_assume"
         | Sig_new_effect
             { mname = uu___; cattributes = uu___1; univs = uu___2;
               binders = uu___3; signature = uu___4; combinators = uu___5;
               actions = uu___6; eff_attrs = uu___7;
               extraction_mode = uu___8;_}
             -> "Sig_new_effect"
         | Sig_sub_effect
             { source = uu___; target = uu___1; lift_wp = uu___2;
               lift = uu___3; kind = uu___4;_}
             -> "Sig_sub_effect"
         | Sig_effect_abbrev
             { lid4 = uu___; us4 = uu___1; bs2 = uu___2; comp1 = uu___3;
               cflags = uu___4;_}
             -> "Sig_effect_abbrev"
         | Sig_pragma uu___ -> "Sig_pragma"
         | Sig_splice { is_typed = uu___; lids2 = uu___1; tac = uu___2;_} ->
             "Sig_splice"
         | Sig_polymonadic_bind
             { m_lid = uu___; n_lid = uu___1; p_lid = uu___2; tm3 = uu___3;
               typ = uu___4; kind1 = uu___5;_}
             -> "Sig_polymonadic_bind"
         | Sig_polymonadic_subcomp
             { m_lid1 = uu___; n_lid1 = uu___1; tm4 = uu___2; typ1 = uu___3;
               kind2 = uu___4;_}
             -> "Sig_polymonadic_subcomp"
         | Sig_fail { errs = uu___; fail_in_lax = uu___1; ses1 = uu___2;_} ->
             "Sig_fail")
  }