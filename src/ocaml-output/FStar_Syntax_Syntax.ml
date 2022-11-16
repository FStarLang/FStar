open Prims
type 'a withinfo_t = {
  v: 'a ;
  p: FStar_Compiler_Range.range }[@@deriving yojson,show]
let __proj__Mkwithinfo_t__item__v : 'a . 'a withinfo_t -> 'a =
  fun projectee -> match projectee with | { v; p;_} -> v
let __proj__Mkwithinfo_t__item__p :
  'a . 'a withinfo_t -> FStar_Compiler_Range.range =
  fun projectee -> match projectee with | { v; p;_} -> p
type var = FStar_Ident.lident withinfo_t[@@deriving yojson,show]
type sconst = FStar_Const.sconst[@@deriving yojson,show]
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | PrintEffectsGraph [@@deriving yojson,show]
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
type 'a memo =
  (('a FStar_Pervasives_Native.option FStar_Compiler_Effect.ref)[@printer
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
  | U_name of FStar_Ident.ident 
  | U_unif of (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar
  * version * FStar_Compiler_Range.range) 
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
let (__proj__U_name__item___0 : universe -> FStar_Ident.ident) =
  fun projectee -> match projectee with | U_name _0 -> _0
let (uu___is_U_unif : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_unif _0 -> true | uu___ -> false
let (__proj__U_unif__item___0 :
  universe ->
    (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version
      * FStar_Compiler_Range.range))
  = fun projectee -> match projectee with | U_unif _0 -> _0
let (uu___is_U_unknown : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_unknown -> true | uu___ -> false
type univ_name = FStar_Ident.ident[@@deriving yojson,show]
type universe_uvar =
  (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version *
    FStar_Compiler_Range.range)[@@deriving yojson,show]
type univ_names = univ_name Prims.list[@@deriving yojson,show]
type universes = universe Prims.list[@@deriving yojson,show]
type monad_name = FStar_Ident.lident[@@deriving yojson,show]
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
  | SomeUseRange of FStar_Compiler_Range.range [@@deriving yojson,show]
let (uu___is_NoUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee -> match projectee with | NoUseRange -> true | uu___ -> false
let (uu___is_SomeUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee ->
    match projectee with | SomeUseRange _0 -> true | uu___ -> false
let (__proj__SomeUseRange__item___0 :
  maybe_set_use_range -> FStar_Compiler_Range.range) =
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
type term' =
  | Tm_bvar of bv 
  | Tm_name of bv 
  | Tm_fvar of fv 
  | Tm_uinst of (term' syntax * universes) 
  | Tm_constant of sconst 
  | Tm_type of universe 
  | Tm_abs of (binder Prims.list * term' syntax * residual_comp
  FStar_Pervasives_Native.option) 
  | Tm_arrow of (binder Prims.list * comp' syntax) 
  | Tm_refine of (bv * term' syntax) 
  | Tm_app of (term' syntax * (term' syntax * arg_qualifier
  FStar_Pervasives_Native.option) Prims.list) 
  | Tm_match of (term' syntax * (binder * ((term' syntax, comp' syntax)
  FStar_Pervasives.either * term' syntax FStar_Pervasives_Native.option *
  Prims.bool)) FStar_Pervasives_Native.option * (pat' withinfo_t * term'
  syntax FStar_Pervasives_Native.option * term' syntax) Prims.list *
  residual_comp FStar_Pervasives_Native.option) 
  | Tm_ascribed of (term' syntax * ((term' syntax, comp' syntax)
  FStar_Pervasives.either * term' syntax FStar_Pervasives_Native.option *
  Prims.bool) * FStar_Ident.lident FStar_Pervasives_Native.option) 
  | Tm_let of ((Prims.bool * letbinding Prims.list) * term' syntax) 
  | Tm_uvar of (ctx_uvar * (subst_elt Prims.list Prims.list *
  maybe_set_use_range)) 
  | Tm_delayed of (term' syntax * (subst_elt Prims.list Prims.list *
  maybe_set_use_range)) 
  | Tm_meta of (term' syntax * metadata) 
  | Tm_lazy of lazyinfo 
  | Tm_quoted of (term' syntax * quoteinfo) 
  | Tm_unknown 
and ctx_uvar =
  {
  ctx_uvar_head:
    ((term' syntax FStar_Pervasives_Native.option * uvar_decoration)
      FStar_Unionfind.p_uvar * version * FStar_Compiler_Range.range)
    ;
  ctx_uvar_gamma: binding Prims.list ;
  ctx_uvar_binders: binder Prims.list ;
  ctx_uvar_reason: Prims.string ;
  ctx_uvar_range: FStar_Compiler_Range.range ;
  ctx_uvar_meta: ctx_uvar_meta_t FStar_Pervasives_Native.option }
and ctx_uvar_meta_t =
  | Ctx_uvar_meta_tac of (FStar_Compiler_Dyn.dyn * term' syntax) 
  | Ctx_uvar_meta_attr of term' syntax 
and uvar_decoration =
  {
  uvar_decoration_typ: term' syntax ;
  uvar_decoration_typedness_depends_on: ctx_uvar Prims.list ;
  uvar_decoration_should_check: should_check_uvar }
and pat' =
  | Pat_constant of sconst 
  | Pat_cons of (fv * universes FStar_Pervasives_Native.option * (pat'
  withinfo_t * Prims.bool) Prims.list) 
  | Pat_var of bv 
  | Pat_wild of bv 
  | Pat_dot_term of term' syntax FStar_Pervasives_Native.option 
and letbinding =
  {
  lbname: (bv, fv) FStar_Pervasives.either ;
  lbunivs: univ_name Prims.list ;
  lbtyp: term' syntax ;
  lbeff: FStar_Ident.lident ;
  lbdef: term' syntax ;
  lbattrs: term' syntax Prims.list ;
  lbpos: FStar_Compiler_Range.range }
and quoteinfo =
  {
  qkind: quote_kind ;
  antiquotes: (bv * term' syntax) Prims.list }
and comp_typ =
  {
  comp_univs: universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: term' syntax ;
  effect_args:
    (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list ;
  flags: cflag Prims.list }
and comp' =
  | Total of (term' syntax * universe FStar_Pervasives_Native.option) 
  | GTotal of (term' syntax * universe FStar_Pervasives_Native.option) 
  | Comp of comp_typ 
and binder =
  {
  binder_bv: bv ;
  binder_qual: binder_qualifier FStar_Pervasives_Native.option ;
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
  | Meta_named of FStar_Ident.lident 
  | Meta_labeled of (Prims.string * FStar_Compiler_Range.range * Prims.bool)
  
  | Meta_desugared of meta_source_info 
  | Meta_monadic of (monad_name * term' syntax) 
  | Meta_monadic_lift of (monad_name * monad_name * term' syntax) 
and meta_source_info =
  | Sequence 
  | Primop 
  | Masked_effect 
  | Meta_smt_pat 
  | Machine_integer of (FStar_Const.signedness * FStar_Const.width) 
and fv_qual =
  | Data_ctor 
  | Record_projector of (FStar_Ident.lident * FStar_Ident.ident) 
  | Record_ctor of (FStar_Ident.lident * FStar_Ident.ident Prims.list) 
  | Unresolved_projector of fv FStar_Pervasives_Native.option 
  | Unresolved_constructor of unresolved_constructor 
and unresolved_constructor =
  {
  uc_base_term: Prims.bool ;
  uc_typename: FStar_Ident.lident FStar_Pervasives_Native.option ;
  uc_fields: FStar_Ident.lident Prims.list }
and subst_elt =
  | DB of (Prims.int * bv) 
  | NM of (bv * Prims.int) 
  | NT of (bv * term' syntax) 
  | UN of (Prims.int * universe) 
  | UD of (univ_name * Prims.int) 
and 'a syntax =
  {
  n: 'a ;
  pos: FStar_Compiler_Range.range ;
  vars: free_vars memo ;
  hash_code: FStar_Hash.hash_code memo }
and bv = {
  ppname: FStar_Ident.ident ;
  index: Prims.int ;
  sort: term' syntax }
and fv =
  {
  fv_name: var ;
  fv_delta: delta_depth ;
  fv_qual: fv_qual FStar_Pervasives_Native.option }
and free_vars =
  {
  free_names: bv Prims.list ;
  free_uvars: ctx_uvar Prims.list ;
  free_univs: universe_uvar Prims.list ;
  free_univ_names: univ_name Prims.list }
and residual_comp =
  {
  residual_effect: FStar_Ident.lident ;
  residual_typ: term' syntax FStar_Pervasives_Native.option ;
  residual_flags: cflag Prims.list }
and lazyinfo =
  {
  blob: FStar_Compiler_Dyn.dyn ;
  lkind: lazy_kind ;
  ltyp: term' syntax ;
  rng: FStar_Compiler_Range.range }
and lazy_kind =
  | BadLazy 
  | Lazy_bv 
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
  | Lazy_embedding of (emb_typ * term' syntax FStar_Thunk.t) 
  | Lazy_universe 
  | Lazy_universe_uvar 
and binding =
  | Binding_var of bv 
  | Binding_lid of (FStar_Ident.lident * (univ_names * term' syntax)) 
  | Binding_univ of univ_name 
and binder_qualifier =
  | Implicit of Prims.bool 
  | Meta of term' syntax 
  | Equality 
and arg_qualifier =
  {
  aqual_implicit: Prims.bool ;
  aqual_attributes: term' syntax Prims.list }
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
let (__proj__Tm_abs__item___0 :
  term' ->
    (binder Prims.list * term' syntax * residual_comp
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tm_abs _0 -> _0
let (uu___is_Tm_arrow : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_arrow _0 -> true | uu___ -> false
let (__proj__Tm_arrow__item___0 :
  term' -> (binder Prims.list * comp' syntax)) =
  fun projectee -> match projectee with | Tm_arrow _0 -> _0
let (uu___is_Tm_refine : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_refine _0 -> true | uu___ -> false
let (__proj__Tm_refine__item___0 : term' -> (bv * term' syntax)) =
  fun projectee -> match projectee with | Tm_refine _0 -> _0
let (uu___is_Tm_app : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_app _0 -> true | uu___ -> false
let (__proj__Tm_app__item___0 :
  term' ->
    (term' syntax * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee -> match projectee with | Tm_app _0 -> _0
let (uu___is_Tm_match : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_match _0 -> true | uu___ -> false
let (__proj__Tm_match__item___0 :
  term' ->
    (term' syntax * (binder * ((term' syntax, comp' syntax)
      FStar_Pervasives.either * term' syntax FStar_Pervasives_Native.option *
      Prims.bool)) FStar_Pervasives_Native.option * (pat' withinfo_t * term'
      syntax FStar_Pervasives_Native.option * term' syntax) Prims.list *
      residual_comp FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tm_match _0 -> _0
let (uu___is_Tm_ascribed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_ascribed _0 -> true | uu___ -> false
let (__proj__Tm_ascribed__item___0 :
  term' ->
    (term' syntax * ((term' syntax, comp' syntax) FStar_Pervasives.either *
      term' syntax FStar_Pervasives_Native.option * Prims.bool) *
      FStar_Ident.lident FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tm_ascribed _0 -> _0
let (uu___is_Tm_let : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_let _0 -> true | uu___ -> false
let (__proj__Tm_let__item___0 :
  term' -> ((Prims.bool * letbinding Prims.list) * term' syntax)) =
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
let (__proj__Tm_delayed__item___0 :
  term' ->
    (term' syntax * (subst_elt Prims.list Prims.list * maybe_set_use_range)))
  = fun projectee -> match projectee with | Tm_delayed _0 -> _0
let (uu___is_Tm_meta : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tm_meta _0 -> true | uu___ -> false
let (__proj__Tm_meta__item___0 : term' -> (term' syntax * metadata)) =
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
      FStar_Unionfind.p_uvar * version * FStar_Compiler_Range.range))
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
  ctx_uvar -> FStar_Compiler_Range.range) =
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
let (__proj__Ctx_uvar_meta_tac__item___0 :
  ctx_uvar_meta_t -> (FStar_Compiler_Dyn.dyn * term' syntax)) =
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
        uvar_decoration_should_check;_} -> uvar_decoration_typ
let (__proj__Mkuvar_decoration__item__uvar_decoration_typedness_depends_on :
  uvar_decoration -> ctx_uvar Prims.list) =
  fun projectee ->
    match projectee with
    | { uvar_decoration_typ; uvar_decoration_typedness_depends_on;
        uvar_decoration_should_check;_} ->
        uvar_decoration_typedness_depends_on
let (__proj__Mkuvar_decoration__item__uvar_decoration_should_check :
  uvar_decoration -> should_check_uvar) =
  fun projectee ->
    match projectee with
    | { uvar_decoration_typ; uvar_decoration_typedness_depends_on;
        uvar_decoration_should_check;_} -> uvar_decoration_should_check
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
let (uu___is_Pat_wild : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_wild _0 -> true | uu___ -> false
let (__proj__Pat_wild__item___0 : pat' -> bv) =
  fun projectee -> match projectee with | Pat_wild _0 -> _0
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
let (__proj__Mkletbinding__item__lbeff : letbinding -> FStar_Ident.lident) =
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
  letbinding -> FStar_Compiler_Range.range) =
  fun projectee ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbpos
let (__proj__Mkquoteinfo__item__qkind : quoteinfo -> quote_kind) =
  fun projectee -> match projectee with | { qkind; antiquotes;_} -> qkind
let (__proj__Mkquoteinfo__item__antiquotes :
  quoteinfo -> (bv * term' syntax) Prims.list) =
  fun projectee ->
    match projectee with | { qkind; antiquotes;_} -> antiquotes
let (__proj__Mkcomp_typ__item__comp_univs : comp_typ -> universes) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
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
let (__proj__Total__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Total _0 -> _0
let (uu___is_GTotal : comp' -> Prims.bool) =
  fun projectee -> match projectee with | GTotal _0 -> true | uu___ -> false
let (__proj__GTotal__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | GTotal _0 -> _0
let (uu___is_Comp : comp' -> Prims.bool) =
  fun projectee -> match projectee with | Comp _0 -> true | uu___ -> false
let (__proj__Comp__item___0 : comp' -> comp_typ) =
  fun projectee -> match projectee with | Comp _0 -> _0
let (__proj__Mkbinder__item__binder_bv : binder -> bv) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_attrs;_} -> binder_bv
let (__proj__Mkbinder__item__binder_qual :
  binder -> binder_qualifier FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_attrs;_} -> binder_qual
let (__proj__Mkbinder__item__binder_attrs :
  binder -> term' syntax Prims.list) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_attrs;_} -> binder_attrs
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
let (__proj__Meta_named__item___0 : metadata -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Meta_named _0 -> _0
let (uu___is_Meta_labeled : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_labeled _0 -> true | uu___ -> false
let (__proj__Meta_labeled__item___0 :
  metadata -> (Prims.string * FStar_Compiler_Range.range * Prims.bool)) =
  fun projectee -> match projectee with | Meta_labeled _0 -> _0
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
  meta_source_info -> (FStar_Const.signedness * FStar_Const.width)) =
  fun projectee -> match projectee with | Machine_integer _0 -> _0
let (uu___is_Data_ctor : fv_qual -> Prims.bool) =
  fun projectee -> match projectee with | Data_ctor -> true | uu___ -> false
let (uu___is_Record_projector : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_projector _0 -> true | uu___ -> false
let (__proj__Record_projector__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Record_projector _0 -> _0
let (uu___is_Record_ctor : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_ctor _0 -> true | uu___ -> false
let (__proj__Record_ctor__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident Prims.list)) =
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
  unresolved_constructor -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { uc_base_term; uc_typename; uc_fields;_} -> uc_typename
let (__proj__Mkunresolved_constructor__item__uc_fields :
  unresolved_constructor -> FStar_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with
    | { uc_base_term; uc_typename; uc_fields;_} -> uc_fields
let (uu___is_DB : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | DB _0 -> true | uu___ -> false
let (__proj__DB__item___0 : subst_elt -> (Prims.int * bv)) =
  fun projectee -> match projectee with | DB _0 -> _0
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
  'a . 'a syntax -> FStar_Compiler_Range.range =
  fun projectee -> match projectee with | { n; pos; vars; hash_code;_} -> pos
let __proj__Mksyntax__item__vars : 'a . 'a syntax -> free_vars memo =
  fun projectee ->
    match projectee with | { n; pos; vars; hash_code;_} -> vars
let __proj__Mksyntax__item__hash_code :
  'a . 'a syntax -> FStar_Hash.hash_code memo =
  fun projectee ->
    match projectee with | { n; pos; vars; hash_code;_} -> hash_code
let (__proj__Mkbv__item__ppname : bv -> FStar_Ident.ident) =
  fun projectee -> match projectee with | { ppname; index; sort;_} -> ppname
let (__proj__Mkbv__item__index : bv -> Prims.int) =
  fun projectee -> match projectee with | { ppname; index; sort;_} -> index
let (__proj__Mkbv__item__sort : bv -> term' syntax) =
  fun projectee -> match projectee with | { ppname; index; sort;_} -> sort
let (__proj__Mkfv__item__fv_name : fv -> var) =
  fun projectee ->
    match projectee with
    | { fv_name; fv_delta; fv_qual = fv_qual1;_} -> fv_name
let (__proj__Mkfv__item__fv_delta : fv -> delta_depth) =
  fun projectee ->
    match projectee with
    | { fv_name; fv_delta; fv_qual = fv_qual1;_} -> fv_delta
let (__proj__Mkfv__item__fv_qual :
  fv -> fv_qual FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { fv_name; fv_delta; fv_qual = fv_qual1;_} -> fv_qual1
let (__proj__Mkfree_vars__item__free_names : free_vars -> bv Prims.list) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_names
let (__proj__Mkfree_vars__item__free_uvars :
  free_vars -> ctx_uvar Prims.list) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_uvars
let (__proj__Mkfree_vars__item__free_univs :
  free_vars -> universe_uvar Prims.list) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_univs
let (__proj__Mkfree_vars__item__free_univ_names :
  free_vars -> univ_name Prims.list) =
  fun projectee ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} ->
        free_univ_names
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
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
let (__proj__Mklazyinfo__item__blob : lazyinfo -> FStar_Compiler_Dyn.dyn) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> blob
let (__proj__Mklazyinfo__item__lkind : lazyinfo -> lazy_kind) =
  fun projectee ->
    match projectee with | { blob; lkind; ltyp; rng;_} -> lkind
let (__proj__Mklazyinfo__item__ltyp : lazyinfo -> term' syntax) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> ltyp
let (__proj__Mklazyinfo__item__rng : lazyinfo -> FStar_Compiler_Range.range)
  =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> rng
let (uu___is_BadLazy : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | BadLazy -> true | uu___ -> false
let (uu___is_Lazy_bv : lazy_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lazy_bv -> true | uu___ -> false
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
  lazy_kind -> (emb_typ * term' syntax FStar_Thunk.t)) =
  fun projectee -> match projectee with | Lazy_embedding _0 -> _0
let (uu___is_Lazy_universe : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_universe -> true | uu___ -> false
let (uu___is_Lazy_universe_uvar : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_universe_uvar -> true | uu___ -> false
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_var _0 -> true | uu___ -> false
let (__proj__Binding_var__item___0 : binding -> bv) =
  fun projectee -> match projectee with | Binding_var _0 -> _0
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_lid _0 -> true | uu___ -> false
let (__proj__Binding_lid__item___0 :
  binding -> (FStar_Ident.lident * (univ_names * term' syntax))) =
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
    FStar_Unionfind.p_uvar * version * FStar_Compiler_Range.range)
type uvars = ctx_uvar FStar_Compiler_Util.set
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
type antiquotations = (bv * term' syntax) Prims.list
type typ = term' syntax
type aqual = arg_qualifier FStar_Pervasives_Native.option
type arg = (term' syntax * arg_qualifier FStar_Pervasives_Native.option)
type args =
  (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list
type binders = binder Prims.list
type lbname = (bv, fv) FStar_Pervasives.either
type letbindings = (Prims.bool * letbinding Prims.list)
type freenames = bv FStar_Compiler_Util.set
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
  | Visible_default 
  | Irreducible 
  | Inline_for_extraction 
  | NoExtract 
  | Noeq 
  | Unopteq 
  | TotalEffect 
  | Logic 
  | Reifiable 
  | Reflectable of FStar_Ident.lident 
  | Discriminator of FStar_Ident.lident 
  | Projector of (FStar_Ident.lident * FStar_Ident.ident) 
  | RecordType of (FStar_Ident.ident Prims.list * FStar_Ident.ident
  Prims.list) 
  | RecordConstructor of (FStar_Ident.ident Prims.list * FStar_Ident.ident
  Prims.list) 
  | Action of FStar_Ident.lident 
  | ExceptionConstructor 
  | HasMaskedEffect 
  | Effect 
  | OnlyName 
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
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Visible_default -> true | uu___ -> false
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
let (__proj__Reflectable__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Reflectable _0 -> _0
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Discriminator _0 -> true | uu___ -> false
let (__proj__Discriminator__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Discriminator _0 -> _0
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu___ -> false
let (__proj__Projector__item___0 :
  qualifier -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordType _0 -> true | uu___ -> false
let (__proj__RecordType__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordType _0 -> _0
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordConstructor _0 -> true | uu___ -> false
let (__proj__RecordConstructor__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordConstructor _0 -> _0
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Action _0 -> true | uu___ -> false
let (__proj__Action__item___0 : qualifier -> FStar_Ident.lident) =
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
type tycon = (FStar_Ident.lident * binders * typ)
type monad_abbrev = {
  mabbrev: FStar_Ident.lident ;
  parms: binders ;
  def: typ }
let (__proj__Mkmonad_abbrev__item__mabbrev :
  monad_abbrev -> FStar_Ident.lident) =
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
type indexed_effect_combinator_kind =
  | Substitutive_combinator of indexed_effect_binder_kind Prims.list 
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
let (uu___is_Ad_hoc_combinator :
  indexed_effect_combinator_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Ad_hoc_combinator -> true | uu___ -> false
type sub_eff =
  {
  source: FStar_Ident.lident ;
  target: FStar_Ident.lident ;
  lift_wp: tscheme FStar_Pervasives_Native.option ;
  lift: tscheme FStar_Pervasives_Native.option ;
  kind: indexed_effect_combinator_kind FStar_Pervasives_Native.option }
let (__proj__Mksub_eff__item__source : sub_eff -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift; kind;_} -> source
let (__proj__Mksub_eff__item__target : sub_eff -> FStar_Ident.lident) =
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
  action_name: FStar_Ident.lident ;
  action_unqualified_name: FStar_Ident.ident ;
  action_univs: univ_names ;
  action_params: binders ;
  action_defn: term ;
  action_typ: typ }
let (__proj__Mkaction__item__action_name : action -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_name
let (__proj__Mkaction__item__action_unqualified_name :
  action -> FStar_Ident.ident) =
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
    }
let (__proj__Mklayered_eff_combinators__item__l_repr :
  layered_eff_combinators -> (tscheme * tscheme)) =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else;_} -> l_repr
let (__proj__Mklayered_eff_combinators__item__l_return :
  layered_eff_combinators -> (tscheme * tscheme)) =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else;_} -> l_return
let (__proj__Mklayered_eff_combinators__item__l_bind :
  layered_eff_combinators ->
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else;_} -> l_bind
let (__proj__Mklayered_eff_combinators__item__l_subcomp :
  layered_eff_combinators ->
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else;_} -> l_subcomp
let (__proj__Mklayered_eff_combinators__item__l_if_then_else :
  layered_eff_combinators ->
    (tscheme * tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else;_} ->
        l_if_then_else
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
type eff_decl =
  {
  mname: FStar_Ident.lident ;
  cattributes: cflag Prims.list ;
  univs: univ_names ;
  binders: binders ;
  signature: effect_signature ;
  combinators: eff_combinators ;
  actions: action Prims.list ;
  eff_attrs: attribute Prims.list }
let (__proj__Mkeff_decl__item__mname : eff_decl -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> mname
let (__proj__Mkeff_decl__item__cattributes : eff_decl -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> cattributes
let (__proj__Mkeff_decl__item__univs : eff_decl -> univ_names) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> univs
let (__proj__Mkeff_decl__item__binders : eff_decl -> binders) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> binders1
let (__proj__Mkeff_decl__item__signature : eff_decl -> effect_signature) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> signature
let (__proj__Mkeff_decl__item__combinators : eff_decl -> eff_combinators) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> combinators
let (__proj__Mkeff_decl__item__actions : eff_decl -> action Prims.list) =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> actions
let (__proj__Mkeff_decl__item__eff_attrs : eff_decl -> attribute Prims.list)
  =
  fun projectee ->
    match projectee with
    | { mname; cattributes; univs; binders = binders1; signature;
        combinators; actions; eff_attrs;_} -> eff_attrs
type sig_metadata =
  {
  sigmeta_active: Prims.bool ;
  sigmeta_fact_db_ids: Prims.string Prims.list ;
  sigmeta_admit: Prims.bool }
let (__proj__Mksig_metadata__item__sigmeta_active :
  sig_metadata -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit;_} ->
        sigmeta_active
let (__proj__Mksig_metadata__item__sigmeta_fact_db_ids :
  sig_metadata -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit;_} ->
        sigmeta_fact_db_ids
let (__proj__Mksig_metadata__item__sigmeta_admit :
  sig_metadata -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit;_} ->
        sigmeta_admit
type sigelt' =
  | Sig_inductive_typ of (FStar_Ident.lident * univ_names * binders * typ *
  FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list) 
  | Sig_bundle of (sigelt Prims.list * FStar_Ident.lident Prims.list) 
  | Sig_datacon of (FStar_Ident.lident * univ_names * typ *
  FStar_Ident.lident * Prims.int * FStar_Ident.lident Prims.list) 
  | Sig_declare_typ of (FStar_Ident.lident * univ_names * typ) 
  | Sig_let of (letbindings * FStar_Ident.lident Prims.list) 
  | Sig_assume of (FStar_Ident.lident * univ_names * formula) 
  | Sig_new_effect of eff_decl 
  | Sig_sub_effect of sub_eff 
  | Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp *
  cflag Prims.list) 
  | Sig_pragma of pragma 
  | Sig_splice of (FStar_Ident.lident Prims.list * term) 
  | Sig_polymonadic_bind of (FStar_Ident.lident * FStar_Ident.lident *
  FStar_Ident.lident * tscheme * tscheme * indexed_effect_combinator_kind
  FStar_Pervasives_Native.option) 
  | Sig_polymonadic_subcomp of (FStar_Ident.lident * FStar_Ident.lident *
  tscheme * tscheme * indexed_effect_combinator_kind
  FStar_Pervasives_Native.option) 
  | Sig_fail of (Prims.int Prims.list * Prims.bool * sigelt Prims.list) 
and sigelt =
  {
  sigel: sigelt' ;
  sigrng: FStar_Compiler_Range.range ;
  sigquals: qualifier Prims.list ;
  sigmeta: sig_metadata ;
  sigattrs: attribute Prims.list ;
  sigopts: FStar_VConfig.vconfig FStar_Pervasives_Native.option }
let (uu___is_Sig_inductive_typ : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_inductive_typ _0 -> true | uu___ -> false
let (__proj__Sig_inductive_typ__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident
      Prims.list * FStar_Ident.lident Prims.list))
  = fun projectee -> match projectee with | Sig_inductive_typ _0 -> _0
let (uu___is_Sig_bundle : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_bundle _0 -> true | uu___ -> false
let (__proj__Sig_bundle__item___0 :
  sigelt' -> (sigelt Prims.list * FStar_Ident.lident Prims.list)) =
  fun projectee -> match projectee with | Sig_bundle _0 -> _0
let (uu___is_Sig_datacon : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_datacon _0 -> true | uu___ -> false
let (__proj__Sig_datacon__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int *
      FStar_Ident.lident Prims.list))
  = fun projectee -> match projectee with | Sig_datacon _0 -> _0
let (uu___is_Sig_declare_typ : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_declare_typ _0 -> true | uu___ -> false
let (__proj__Sig_declare_typ__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * typ)) =
  fun projectee -> match projectee with | Sig_declare_typ _0 -> _0
let (uu___is_Sig_let : sigelt' -> Prims.bool) =
  fun projectee -> match projectee with | Sig_let _0 -> true | uu___ -> false
let (__proj__Sig_let__item___0 :
  sigelt' -> (letbindings * FStar_Ident.lident Prims.list)) =
  fun projectee -> match projectee with | Sig_let _0 -> _0
let (uu___is_Sig_assume : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_assume _0 -> true | uu___ -> false
let (__proj__Sig_assume__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * formula)) =
  fun projectee -> match projectee with | Sig_assume _0 -> _0
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
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * comp * cflag Prims.list))
  = fun projectee -> match projectee with | Sig_effect_abbrev _0 -> _0
let (uu___is_Sig_pragma : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_pragma _0 -> true | uu___ -> false
let (__proj__Sig_pragma__item___0 : sigelt' -> pragma) =
  fun projectee -> match projectee with | Sig_pragma _0 -> _0
let (uu___is_Sig_splice : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_splice _0 -> true | uu___ -> false
let (__proj__Sig_splice__item___0 :
  sigelt' -> (FStar_Ident.lident Prims.list * term)) =
  fun projectee -> match projectee with | Sig_splice _0 -> _0
let (uu___is_Sig_polymonadic_bind : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_polymonadic_bind _0 -> true | uu___ -> false
let (__proj__Sig_polymonadic_bind__item___0 :
  sigelt' ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * tscheme *
      tscheme * indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Sig_polymonadic_bind _0 -> _0
let (uu___is_Sig_polymonadic_subcomp : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Sig_polymonadic_subcomp _0 -> true
    | uu___ -> false
let (__proj__Sig_polymonadic_subcomp__item___0 :
  sigelt' ->
    (FStar_Ident.lident * FStar_Ident.lident * tscheme * tscheme *
      indexed_effect_combinator_kind FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Sig_polymonadic_subcomp _0 -> _0
let (uu___is_Sig_fail : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_fail _0 -> true | uu___ -> false
let (__proj__Sig_fail__item___0 :
  sigelt' -> (Prims.int Prims.list * Prims.bool * sigelt Prims.list)) =
  fun projectee -> match projectee with | Sig_fail _0 -> _0
let (__proj__Mksigelt__item__sigel : sigelt -> sigelt') =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigel
let (__proj__Mksigelt__item__sigrng : sigelt -> FStar_Compiler_Range.range) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigrng
let (__proj__Mksigelt__item__sigquals : sigelt -> qualifier Prims.list) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigquals
let (__proj__Mksigelt__item__sigmeta : sigelt -> sig_metadata) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigmeta
let (__proj__Mksigelt__item__sigattrs : sigelt -> attribute Prims.list) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigattrs
let (__proj__Mksigelt__item__sigopts :
  sigelt -> FStar_VConfig.vconfig FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigopts
type sigelts = sigelt Prims.list
type modul =
  {
  name: FStar_Ident.lident ;
  declarations: sigelts ;
  is_interface: Prims.bool }
let (__proj__Mkmodul__item__name : modul -> FStar_Ident.lident) =
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
let (lazy_chooser :
  (lazy_kind -> lazyinfo -> term) FStar_Pervasives_Native.option
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (mod_name : modul -> FStar_Ident.lident) = fun m -> m.name
let (contains_reflectable : qualifier Prims.list -> Prims.bool) =
  fun l ->
    FStar_Compiler_Util.for_some
      (fun uu___ ->
         match uu___ with | Reflectable uu___1 -> true | uu___1 -> false) l
let withinfo : 'a . 'a -> FStar_Compiler_Range.range -> 'a withinfo_t =
  fun v -> fun r -> { v; p = r }
let withsort : 'a . 'a -> 'a withinfo_t =
  fun v -> withinfo v FStar_Compiler_Range.dummyRange
let (bv_eq : bv -> bv -> Prims.bool) =
  fun bv1 -> fun bv2 -> bv1.index = bv2.index
let (order_bv : bv -> bv -> Prims.int) =
  fun x ->
    fun y ->
      let i =
        let uu___ = FStar_Ident.string_of_id x.ppname in
        let uu___1 = FStar_Ident.string_of_id y.ppname in
        FStar_String.compare uu___ uu___1 in
      if i = Prims.int_zero then x.index - y.index else i
let (order_ident : FStar_Ident.ident -> FStar_Ident.ident -> Prims.int) =
  fun x ->
    fun y ->
      let uu___ = FStar_Ident.string_of_id x in
      let uu___1 = FStar_Ident.string_of_id y in
      FStar_String.compare uu___ uu___1
let (order_fv : FStar_Ident.lident -> FStar_Ident.lident -> Prims.int) =
  fun x ->
    fun y ->
      let uu___ = FStar_Ident.string_of_lid x in
      let uu___1 = FStar_Ident.string_of_lid y in
      FStar_String.compare uu___ uu___1
let (range_of_lbname : lbname -> FStar_Compiler_Range.range) =
  fun l ->
    match l with
    | FStar_Pervasives.Inl x -> FStar_Ident.range_of_id x.ppname
    | FStar_Pervasives.Inr fv1 -> FStar_Ident.range_of_lid (fv1.fv_name).v
let (range_of_bv : bv -> FStar_Compiler_Range.range) =
  fun x -> FStar_Ident.range_of_id x.ppname
let (set_range_of_bv : bv -> FStar_Compiler_Range.range -> bv) =
  fun x ->
    fun r ->
      let uu___ = FStar_Ident.set_id_range r x.ppname in
      { ppname = uu___; index = (x.index); sort = (x.sort) }
let (on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo) =
  fun f ->
    fun qi ->
      let aq =
        FStar_Compiler_List.map
          (fun uu___ ->
             match uu___ with | (bv1, t) -> let uu___1 = f t in (bv1, uu___1))
          qi.antiquotes in
      { qkind = (qi.qkind); antiquotes = aq }
let (lookup_aq : bv -> antiquotations -> term FStar_Pervasives_Native.option)
  =
  fun bv1 ->
    fun aq ->
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 -> match uu___1 with | (bv', uu___2) -> bv_eq bv1 bv')
          aq in
      match uu___ with
      | FStar_Pervasives_Native.Some (uu___1, e) ->
          FStar_Pervasives_Native.Some e
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let syn :
  'uuuuu 'uuuuu1 'uuuuu2 .
    'uuuuu -> 'uuuuu1 -> ('uuuuu1 -> 'uuuuu -> 'uuuuu2) -> 'uuuuu2
  = fun p -> fun k -> fun f -> f k p
let mk_fvs :
  'uuuuu .
    unit -> 'uuuuu FStar_Pervasives_Native.option FStar_Compiler_Effect.ref
  = fun uu___ -> FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let mk_uvs :
  'uuuuu .
    unit -> 'uuuuu FStar_Pervasives_Native.option FStar_Compiler_Effect.ref
  = fun uu___ -> FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (new_bv_set : unit -> bv FStar_Compiler_Util.set) =
  fun uu___ -> FStar_Compiler_Util.new_set order_bv
let (new_id_set : unit -> FStar_Ident.ident FStar_Compiler_Util.set) =
  fun uu___ -> FStar_Compiler_Util.new_set order_ident
let (new_fv_set : unit -> FStar_Ident.lident FStar_Compiler_Util.set) =
  fun uu___ -> FStar_Compiler_Util.new_set order_fv
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x ->
    fun y ->
      let uu___ = FStar_Ident.string_of_id x in
      let uu___1 = FStar_Ident.string_of_id y in
      FStar_String.compare uu___ uu___1
let (new_universe_names_set : unit -> univ_name FStar_Compiler_Util.set) =
  fun uu___ -> FStar_Compiler_Util.new_set order_univ_name
let (eq_binding : binding -> binding -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (Binding_var bv1, Binding_var bv2) -> bv_eq bv1 bv2
      | (Binding_lid (lid1, uu___), Binding_lid (lid2, uu___1)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1, Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu___ -> false
type path = Prims.string Prims.list
type subst_t = subst_elt Prims.list
let (no_names : freenames) = new_bv_set ()
let (no_fvars : FStar_Ident.lident FStar_Compiler_Util.set) = new_fv_set ()
let (no_universe_names : univ_name FStar_Compiler_Util.set) =
  new_universe_names_set ()
let (freenames_of_list : bv Prims.list -> freenames) =
  fun l ->
    FStar_Compiler_List.fold_right FStar_Compiler_Util.set_add l no_names
let (list_of_freenames : freenames -> bv Prims.list) =
  fun fvs -> FStar_Compiler_Util.set_elements fvs
let mk : 'a . 'a -> FStar_Compiler_Range.range -> 'a syntax =
  fun t ->
    fun r ->
      let uu___ = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
      let uu___1 = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
      { n = t; pos = r; vars = uu___; hash_code = uu___1 }
let (bv_to_tm : bv -> term) =
  fun bv1 -> let uu___ = range_of_bv bv1 in mk (Tm_bvar bv1) uu___
let (bv_to_name : bv -> term) =
  fun bv1 -> let uu___ = range_of_bv bv1 in mk (Tm_name bv1) uu___
let (binders_to_names : binders -> term Prims.list) =
  fun bs ->
    FStar_Compiler_Effect.op_Bar_Greater bs
      (FStar_Compiler_List.map (fun b -> bv_to_name b.binder_bv))
let (mk_Tm_app : term -> args -> FStar_Compiler_Range.range -> term) =
  fun t1 ->
    fun args1 ->
      fun p ->
        match args1 with | [] -> t1 | uu___ -> mk (Tm_app (t1, args1)) p
let (mk_Tm_uinst : term -> universes -> term) =
  fun t ->
    fun us ->
      match t.n with
      | Tm_fvar uu___ ->
          (match us with | [] -> t | us1 -> mk (Tm_uinst (t, us1)) t.pos)
      | uu___ -> failwith "Unexpected universe instantiation"
let (extend_app_n : term -> args -> FStar_Compiler_Range.range -> term) =
  fun t ->
    fun args' ->
      fun r ->
        match t.n with
        | Tm_app (head, args1) ->
            mk_Tm_app head (FStar_Compiler_List.op_At args1 args') r
        | uu___ -> mk_Tm_app t args' r
let (extend_app : term -> arg -> FStar_Compiler_Range.range -> term) =
  fun t -> fun arg1 -> fun r -> extend_app_n t [arg1] r
let (mk_Tm_delayed : (term * subst_ts) -> FStar_Compiler_Range.range -> term)
  = fun lr -> fun pos -> mk (Tm_delayed lr) pos
let (mk_Total' : typ -> universe FStar_Pervasives_Native.option -> comp) =
  fun t -> fun u -> mk (Total (t, u)) t.pos
let (mk_GTotal' : typ -> universe FStar_Pervasives_Native.option -> comp) =
  fun t -> fun u -> mk (GTotal (t, u)) t.pos
let (mk_Total : typ -> comp) =
  fun t -> mk_Total' t FStar_Pervasives_Native.None
let (mk_GTotal : typ -> comp) =
  fun t -> mk_GTotal' t FStar_Pervasives_Native.None
let (mk_Comp : comp_typ -> comp) = fun ct -> mk (Comp ct) (ct.result_typ).pos
let (mk_lb :
  (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term *
    attribute Prims.list * FStar_Compiler_Range.range) -> letbinding)
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
        effect_name = FStar_Parser_Const.effect_Tac_lid;
        result_typ = t;
        effect_args = [];
        flags = [SOMETRIVIAL; TRIVIAL_POSTCONDITION]
      }
let (default_sigmeta : sig_metadata) =
  { sigmeta_active = true; sigmeta_fact_db_ids = []; sigmeta_admit = false }
let (mk_sigelt : sigelt' -> sigelt) =
  fun e ->
    {
      sigel = e;
      sigrng = FStar_Compiler_Range.dummyRange;
      sigquals = [];
      sigmeta = default_sigmeta;
      sigattrs = [];
      sigopts = FStar_Pervasives_Native.None
    }
let (mk_subst : subst_t -> subst_t) = fun s -> s
let (extend_subst : subst_elt -> subst_elt Prims.list -> subst_t) =
  fun x -> fun s -> x :: s
let (argpos : arg -> FStar_Compiler_Range.range) =
  fun x -> (FStar_Pervasives_Native.fst x).pos
let (tun : term) = mk Tm_unknown FStar_Compiler_Range.dummyRange
let (teff : term) =
  mk (Tm_constant FStar_Const.Const_effect) FStar_Compiler_Range.dummyRange
let (is_teff : term -> Prims.bool) =
  fun t ->
    match t.n with
    | Tm_constant (FStar_Const.Const_effect) -> true
    | uu___ -> false
let (is_type : term -> Prims.bool) =
  fun t -> match t.n with | Tm_type uu___ -> true | uu___ -> false
let (null_id : FStar_Ident.ident) =
  FStar_Ident.mk_ident ("_", FStar_Compiler_Range.dummyRange)
let (null_bv : term -> bv) =
  fun k ->
    let uu___ = FStar_Ident.next_id () in
    { ppname = null_id; index = uu___; sort = k }
let (is_null_bv : bv -> Prims.bool) =
  fun b ->
    let uu___ = FStar_Ident.string_of_id b.ppname in
    let uu___1 = FStar_Ident.string_of_id null_id in uu___ = uu___1
let (is_null_binder : binder -> Prims.bool) = fun b -> is_null_bv b.binder_bv
let (range_of_ropt :
  FStar_Compiler_Range.range FStar_Pervasives_Native.option ->
    FStar_Compiler_Range.range)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Compiler_Range.dummyRange
    | FStar_Pervasives_Native.Some r -> r
let (gen_bv :
  Prims.string ->
    FStar_Compiler_Range.range FStar_Pervasives_Native.option -> typ -> bv)
  =
  fun s ->
    fun r ->
      fun t ->
        let id = FStar_Ident.mk_ident (s, (range_of_ropt r)) in
        let uu___ = FStar_Ident.next_id () in
        { ppname = id; index = uu___; sort = t }
let (new_bv :
  FStar_Compiler_Range.range FStar_Pervasives_Native.option -> typ -> bv) =
  fun ropt -> fun t -> gen_bv FStar_Ident.reserved_prefix ropt t
let (freshen_bv : bv -> bv) =
  fun bv1 ->
    let uu___ = is_null_bv bv1 in
    if uu___
    then
      let uu___1 =
        let uu___2 = range_of_bv bv1 in FStar_Pervasives_Native.Some uu___2 in
      new_bv uu___1 bv1.sort
    else
      (let uu___2 = FStar_Ident.next_id () in
       { ppname = (bv1.ppname); index = uu___2; sort = (bv1.sort) })
let (mk_binder_with_attrs : bv -> bqual -> attribute Prims.list -> binder) =
  fun bv1 ->
    fun aqual1 ->
      fun attrs ->
        { binder_bv = bv1; binder_qual = aqual1; binder_attrs = attrs }
let (mk_binder : bv -> binder) =
  fun a -> mk_binder_with_attrs a FStar_Pervasives_Native.None []
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
    FStar_Compiler_List.fold_right
      (fun b -> fun out -> FStar_Compiler_Util.set_add b.binder_bv out) bs
      no_names
let (binders_of_list : bv Prims.list -> binders) =
  fun fvs ->
    FStar_Compiler_Effect.op_Bar_Greater fvs
      (FStar_Compiler_List.map (fun t -> mk_binder t))
let (binders_of_freenames : freenames -> binders) =
  fun fvs ->
    let uu___ = FStar_Compiler_Util.set_elements fvs in
    FStar_Compiler_Effect.op_Bar_Greater uu___ binders_of_list
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
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu___, uu___1, pats) ->
          FStar_Compiler_List.fold_left
            (fun b1 ->
               fun uu___2 -> match uu___2 with | (p2, uu___3) -> aux b1 p2) b
            pats in
    let uu___ = aux [] p in
    FStar_Compiler_Effect.op_Less_Bar FStar_Compiler_List.rev uu___
let (freshen_binder : binder -> binder) =
  fun b ->
    let uu___ = freshen_bv b.binder_bv in
    {
      binder_bv = uu___;
      binder_qual = (b.binder_qual);
      binder_attrs = (b.binder_attrs)
    }
let (new_univ_name :
  FStar_Compiler_Range.range FStar_Pervasives_Native.option -> univ_name) =
  fun ropt ->
    let id = FStar_Ident.next_id () in
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Compiler_Util.string_of_int id in
        Prims.op_Hat FStar_Ident.reserved_prefix uu___2 in
      (uu___1, (range_of_ropt ropt)) in
    FStar_Ident.mk_ident uu___
let (lbname_eq :
  (bv, FStar_Ident.lident) FStar_Pervasives.either ->
    (bv, FStar_Ident.lident) FStar_Pervasives.either -> Prims.bool)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (FStar_Pervasives.Inl x, FStar_Pervasives.Inl y) -> bv_eq x y
      | (FStar_Pervasives.Inr l, FStar_Pervasives.Inr m) ->
          FStar_Ident.lid_equals l m
      | uu___ -> false
let (fv_eq : fv -> fv -> Prims.bool) =
  fun fv1 ->
    fun fv2 -> FStar_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
let (fv_eq_lid : fv -> FStar_Ident.lident -> Prims.bool) =
  fun fv1 -> fun lid -> FStar_Ident.lid_equals (fv1.fv_name).v lid
let (set_bv_range : bv -> FStar_Compiler_Range.range -> bv) =
  fun bv1 ->
    fun r ->
      let uu___ = FStar_Ident.set_id_range r bv1.ppname in
      { ppname = uu___; index = (bv1.index); sort = (bv1.sort) }
let (lid_as_fv :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> fv)
  =
  fun l ->
    fun dd ->
      fun dq ->
        let uu___ =
          let uu___1 = FStar_Ident.range_of_lid l in withinfo l uu___1 in
        { fv_name = uu___; fv_delta = dd; fv_qual = dq }
let (fv_to_tm : fv -> term) =
  fun fv1 ->
    let uu___ = FStar_Ident.range_of_lid (fv1.fv_name).v in
    mk (Tm_fvar fv1) uu___
let (fvar :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> term)
  =
  fun l ->
    fun dd -> fun dq -> let uu___ = lid_as_fv l dd dq in fv_to_tm uu___
let (lid_of_fv : fv -> FStar_Ident.lid) = fun fv1 -> (fv1.fv_name).v
let (range_of_fv : fv -> FStar_Compiler_Range.range) =
  fun fv1 -> let uu___ = lid_of_fv fv1 in FStar_Ident.range_of_lid uu___
let (set_range_of_fv : fv -> FStar_Compiler_Range.range -> fv) =
  fun fv1 ->
    fun r ->
      let uu___ =
        let uu___1 = fv1.fv_name in
        let uu___2 =
          let uu___3 = lid_of_fv fv1 in FStar_Ident.set_lid_range uu___3 r in
        { v = uu___2; p = (uu___1.p) } in
      { fv_name = uu___; fv_delta = (fv1.fv_delta); fv_qual = (fv1.fv_qual) }
let (has_simple_attribute : term Prims.list -> Prims.string -> Prims.bool) =
  fun l ->
    fun s ->
      FStar_Compiler_List.existsb
        (fun uu___ ->
           match uu___ with
           | { n = Tm_constant (FStar_Const.Const_string (data, uu___1));
               pos = uu___2; vars = uu___3; hash_code = uu___4;_} when
               data = s -> true
           | uu___1 -> false) l
let rec (eq_pat : pat -> pat -> Prims.bool) =
  fun p1 ->
    fun p2 ->
      match ((p1.v), (p2.v)) with
      | (Pat_constant c1, Pat_constant c2) -> FStar_Const.eq_const c1 c2
      | (Pat_cons (fv1, us1, as1), Pat_cons (fv2, us2, as2)) ->
          let uu___ =
            (fv_eq fv1 fv2) &&
              ((FStar_Compiler_List.length as1) =
                 (FStar_Compiler_List.length as2)) in
          if uu___
          then
            (FStar_Compiler_List.forall2
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
                    (FStar_Compiler_List.length us11) =
                      (FStar_Compiler_List.length us21)
                | uu___1 -> false))
          else false
      | (Pat_var uu___, Pat_var uu___1) -> true
      | (Pat_wild uu___, Pat_wild uu___1) -> true
      | (Pat_dot_term uu___, Pat_dot_term uu___1) -> true
      | (uu___, uu___1) -> false
let (delta_constant : delta_depth) = Delta_constant_at_level Prims.int_zero
let (delta_equational : delta_depth) =
  Delta_equational_at_level Prims.int_zero
let (fvconst : FStar_Ident.lident -> fv) =
  fun l -> lid_as_fv l delta_constant FStar_Pervasives_Native.None
let (tconst : FStar_Ident.lident -> term) =
  fun l ->
    let uu___ = let uu___1 = fvconst l in Tm_fvar uu___1 in
    mk uu___ FStar_Compiler_Range.dummyRange
let (tabbrev : FStar_Ident.lident -> term) =
  fun l ->
    let uu___ =
      let uu___1 =
        lid_as_fv l (Delta_constant_at_level Prims.int_one)
          FStar_Pervasives_Native.None in
      Tm_fvar uu___1 in
    mk uu___ FStar_Compiler_Range.dummyRange
let (tdataconstr : FStar_Ident.lident -> term) =
  fun l ->
    let uu___ =
      lid_as_fv l delta_constant (FStar_Pervasives_Native.Some Data_ctor) in
    fv_to_tm uu___
let (t_unit : term) = tconst FStar_Parser_Const.unit_lid
let (t_bool : term) = tconst FStar_Parser_Const.bool_lid
let (t_int : term) = tconst FStar_Parser_Const.int_lid
let (t_string : term) = tconst FStar_Parser_Const.string_lid
let (t_exn : term) = tconst FStar_Parser_Const.exn_lid
let (t_real : term) = tconst FStar_Parser_Const.real_lid
let (t_float : term) = tconst FStar_Parser_Const.float_lid
let (t_char : term) = tabbrev FStar_Parser_Const.char_lid
let (t_range : term) = tconst FStar_Parser_Const.range_lid
let (t_vconfig : term) = tconst FStar_Parser_Const.vconfig_lid
let (t_term : term) = tconst FStar_Parser_Const.term_lid
let (t_term_view : term) = tabbrev FStar_Parser_Const.term_view_lid
let (t_order : term) = tconst FStar_Parser_Const.order_lid
let (t_decls : term) = tabbrev FStar_Parser_Const.decls_lid
let (t_binder : term) = tconst FStar_Parser_Const.binder_lid
let (t_binders : term) = tconst FStar_Parser_Const.binders_lid
let (t_bv : term) = tconst FStar_Parser_Const.bv_lid
let (t_fv : term) = tconst FStar_Parser_Const.fv_lid
let (t_norm_step : term) = tconst FStar_Parser_Const.norm_step_lid
let (t_tac_of : term -> term -> term) =
  fun a ->
    fun b ->
      let uu___ =
        let uu___1 = tabbrev FStar_Parser_Const.tac_lid in
        mk_Tm_uinst uu___1 [U_zero; U_zero] in
      let uu___1 =
        let uu___2 = as_arg a in
        let uu___3 = let uu___4 = as_arg b in [uu___4] in uu___2 :: uu___3 in
      mk_Tm_app uu___ uu___1 FStar_Compiler_Range.dummyRange
let (t_tactic_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStar_Parser_Const.tactic_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStar_Compiler_Range.dummyRange
let (t_tactic_unit : term) = t_tactic_of t_unit
let (t_list_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStar_Parser_Const.list_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStar_Compiler_Range.dummyRange
let (t_option_of : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = tabbrev FStar_Parser_Const.option_lid in
      mk_Tm_uinst uu___1 [U_zero] in
    let uu___1 = let uu___2 = as_arg t in [uu___2] in
    mk_Tm_app uu___ uu___1 FStar_Compiler_Range.dummyRange
let (t_tuple2_of : term -> term -> term) =
  fun t1 ->
    fun t2 ->
      let uu___ =
        let uu___1 = tabbrev FStar_Parser_Const.lid_tuple2 in
        mk_Tm_uinst uu___1 [U_zero; U_zero] in
      let uu___1 =
        let uu___2 = as_arg t1 in
        let uu___3 = let uu___4 = as_arg t2 in [uu___4] in uu___2 :: uu___3 in
      mk_Tm_app uu___ uu___1 FStar_Compiler_Range.dummyRange
let (t_tuple3_of : term -> term -> term -> term) =
  fun t1 ->
    fun t2 ->
      fun t3 ->
        let uu___ =
          let uu___1 = tabbrev FStar_Parser_Const.lid_tuple3 in
          mk_Tm_uinst uu___1 [U_zero; U_zero; U_zero] in
        let uu___1 =
          let uu___2 = as_arg t1 in
          let uu___3 =
            let uu___4 = as_arg t2 in
            let uu___5 = let uu___6 = as_arg t3 in [uu___6] in uu___4 ::
              uu___5 in
          uu___2 :: uu___3 in
        mk_Tm_app uu___ uu___1 FStar_Compiler_Range.dummyRange
let (t_either_of : term -> term -> term) =
  fun t1 ->
    fun t2 ->
      let uu___ =
        let uu___1 = tabbrev FStar_Parser_Const.either_lid in
        mk_Tm_uinst uu___1 [U_zero; U_zero] in
      let uu___1 =
        let uu___2 = as_arg t1 in
        let uu___3 = let uu___4 = as_arg t2 in [uu___4] in uu___2 :: uu___3 in
      mk_Tm_app uu___ uu___1 FStar_Compiler_Range.dummyRange
let (unit_const_with_range : FStar_Compiler_Range.range -> term) =
  fun r -> mk (Tm_constant FStar_Const.Const_unit) r
let (unit_const : term) =
  unit_const_with_range FStar_Compiler_Range.dummyRange