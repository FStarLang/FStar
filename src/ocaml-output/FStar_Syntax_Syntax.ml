open Prims
type 'a withinfo_t = {
  v: 'a ;
  p: FStar_Range.range }[@@deriving yojson,show]
let __proj__Mkwithinfo_t__item__v : 'a . 'a withinfo_t -> 'a =
  fun projectee -> match projectee with | { v; p;_} -> v
let __proj__Mkwithinfo_t__item__p : 'a . 'a withinfo_t -> FStar_Range.range =
  fun projectee -> match projectee with | { v; p;_} -> p
type var = FStar_Ident.lident withinfo_t[@@deriving yojson,show]
type sconst = FStar_Const.sconst[@@deriving yojson,show]
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | LightOff [@@deriving yojson,show]
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | SetOptions _0 -> true | uu____169 -> false
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee -> match projectee with | SetOptions _0 -> _0
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ResetOptions _0 -> true | uu____184 -> false
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | ResetOptions _0 -> _0
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PushOptions _0 -> true | uu____205 -> false
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PushOptions _0 -> _0
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PopOptions -> true | uu____223 -> false
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartSolver -> true | uu____229 -> false
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | LightOff -> true | uu____235 -> false
type 'a memo =
  (('a FStar_Pervasives_Native.option FStar_ST.ref)[@printer
                                                     fun fmt ->
                                                       fun _ ->
                                                         Format.pp_print_string
                                                           fmt "None"])
[@@deriving yojson,show]
type emb_typ =
  | ET_abstract 
  | ET_fun of (emb_typ * emb_typ) 
  | ET_app of (Prims.string * emb_typ Prims.list) 
let (uu___is_ET_abstract : emb_typ -> Prims.bool) =
  fun projectee ->
    match projectee with | ET_abstract -> true | uu____269 -> false
let (uu___is_ET_fun : emb_typ -> Prims.bool) =
  fun projectee ->
    match projectee with | ET_fun _0 -> true | uu____280 -> false
let (__proj__ET_fun__item___0 : emb_typ -> (emb_typ * emb_typ)) =
  fun projectee -> match projectee with | ET_fun _0 -> _0
let (uu___is_ET_app : emb_typ -> Prims.bool) =
  fun projectee ->
    match projectee with | ET_app _0 -> true | uu____311 -> false
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
  * version * FStar_Range.range) 
  | U_unknown [@@deriving yojson,show]
let (uu___is_U_zero : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_zero -> true | uu____402 -> false
let (uu___is_U_succ : universe -> Prims.bool) =
  fun projectee ->
    match projectee with | U_succ _0 -> true | uu____409 -> false
let (__proj__U_succ__item___0 : universe -> universe) =
  fun projectee -> match projectee with | U_succ _0 -> _0
let (uu___is_U_max : universe -> Prims.bool) =
  fun projectee ->
    match projectee with | U_max _0 -> true | uu____424 -> false
let (__proj__U_max__item___0 : universe -> universe Prims.list) =
  fun projectee -> match projectee with | U_max _0 -> _0
let (uu___is_U_bvar : universe -> Prims.bool) =
  fun projectee ->
    match projectee with | U_bvar _0 -> true | uu____443 -> false
let (__proj__U_bvar__item___0 : universe -> Prims.int) =
  fun projectee -> match projectee with | U_bvar _0 -> _0
let (uu___is_U_name : universe -> Prims.bool) =
  fun projectee ->
    match projectee with | U_name _0 -> true | uu____456 -> false
let (__proj__U_name__item___0 : universe -> FStar_Ident.ident) =
  fun projectee -> match projectee with | U_name _0 -> _0
let (uu___is_U_unif : universe -> Prims.bool) =
  fun projectee ->
    match projectee with | U_unif _0 -> true | uu____479 -> false
let (__proj__U_unif__item___0 :
  universe ->
    (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version
      * FStar_Range.range))
  = fun projectee -> match projectee with | U_unif _0 -> _0
let (uu___is_U_unknown : universe -> Prims.bool) =
  fun projectee ->
    match projectee with | U_unknown -> true | uu____521 -> false
type univ_name = FStar_Ident.ident[@@deriving yojson,show]
type universe_uvar =
  (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version *
    FStar_Range.range)[@@deriving yojson,show]
type univ_names = univ_name Prims.list[@@deriving yojson,show]
type universes = universe Prims.list[@@deriving yojson,show]
type monad_name = FStar_Ident.lident[@@deriving yojson,show]
type quote_kind =
  | Quote_static 
  | Quote_dynamic [@@deriving yojson,show]
let (uu___is_Quote_static : quote_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote_static -> true | uu____541 -> false
let (uu___is_Quote_dynamic : quote_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote_dynamic -> true | uu____547 -> false
type maybe_set_use_range =
  | NoUseRange 
  | SomeUseRange of FStar_Range.range [@@deriving yojson,show]
let (uu___is_NoUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee ->
    match projectee with | NoUseRange -> true | uu____558 -> false
let (uu___is_SomeUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee ->
    match projectee with | SomeUseRange _0 -> true | uu____565 -> false
let (__proj__SomeUseRange__item___0 :
  maybe_set_use_range -> FStar_Range.range) =
  fun projectee -> match projectee with | SomeUseRange _0 -> _0
type delta_depth =
  | Delta_constant_at_level of Prims.int 
  | Delta_equational_at_level of Prims.int 
  | Delta_abstract of delta_depth [@@deriving yojson,show]
let (uu___is_Delta_constant_at_level : delta_depth -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Delta_constant_at_level _0 -> true
    | uu____593 -> false
let (__proj__Delta_constant_at_level__item___0 : delta_depth -> Prims.int) =
  fun projectee -> match projectee with | Delta_constant_at_level _0 -> _0
let (uu___is_Delta_equational_at_level : delta_depth -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Delta_equational_at_level _0 -> true
    | uu____606 -> false
let (__proj__Delta_equational_at_level__item___0 : delta_depth -> Prims.int)
  =
  fun projectee -> match projectee with | Delta_equational_at_level _0 -> _0
let (uu___is_Delta_abstract : delta_depth -> Prims.bool) =
  fun projectee ->
    match projectee with | Delta_abstract _0 -> true | uu____619 -> false
let (__proj__Delta_abstract__item___0 : delta_depth -> delta_depth) =
  fun projectee -> match projectee with | Delta_abstract _0 -> _0
type should_check_uvar =
  | Allow_unresolved 
  | Allow_untyped 
  | Strict [@@deriving yojson,show]
let (uu___is_Allow_unresolved : should_check_uvar -> Prims.bool) =
  fun projectee ->
    match projectee with | Allow_unresolved -> true | uu____631 -> false
let (uu___is_Allow_untyped : should_check_uvar -> Prims.bool) =
  fun projectee ->
    match projectee with | Allow_untyped -> true | uu____637 -> false
let (uu___is_Strict : should_check_uvar -> Prims.bool) =
  fun projectee -> match projectee with | Strict -> true | uu____643 -> false
type term' =
  | Tm_bvar of bv 
  | Tm_name of bv 
  | Tm_fvar of fv 
  | Tm_uinst of (term' syntax * universes) 
  | Tm_constant of sconst 
  | Tm_type of universe 
  | Tm_abs of ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list
  * term' syntax * residual_comp FStar_Pervasives_Native.option) 
  | Tm_arrow of ((bv * arg_qualifier FStar_Pervasives_Native.option)
  Prims.list * comp' syntax) 
  | Tm_refine of (bv * term' syntax) 
  | Tm_app of (term' syntax * (term' syntax * arg_qualifier
  FStar_Pervasives_Native.option) Prims.list) 
  | Tm_match of (term' syntax * (pat' withinfo_t * term' syntax
  FStar_Pervasives_Native.option * term' syntax) Prims.list) 
  | Tm_ascribed of (term' syntax * ((term' syntax, comp' syntax)
  FStar_Util.either * term' syntax FStar_Pervasives_Native.option) *
  FStar_Ident.lident FStar_Pervasives_Native.option) 
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
    (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
      version * FStar_Range.range)
    ;
  ctx_uvar_gamma: binding Prims.list ;
  ctx_uvar_binders:
    (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list ;
  ctx_uvar_typ: term' syntax ;
  ctx_uvar_reason: Prims.string ;
  ctx_uvar_should_check: should_check_uvar ;
  ctx_uvar_range: FStar_Range.range ;
  ctx_uvar_meta: ctx_uvar_meta_t FStar_Pervasives_Native.option }
and ctx_uvar_meta_t =
  | Ctx_uvar_meta_tac of (FStar_Dyn.dyn * term' syntax) 
  | Ctx_uvar_meta_attr of term' syntax 
and pat' =
  | Pat_constant of sconst 
  | Pat_cons of (fv * (pat' withinfo_t * Prims.bool) Prims.list) 
  | Pat_var of bv 
  | Pat_wild of bv 
  | Pat_dot_term of (bv * term' syntax) 
and letbinding =
  {
  lbname: (bv, fv) FStar_Util.either ;
  lbunivs: univ_name Prims.list ;
  lbtyp: term' syntax ;
  lbeff: FStar_Ident.lident ;
  lbdef: term' syntax ;
  lbattrs: term' syntax Prims.list ;
  lbpos: FStar_Range.range }
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
  | DECREASES of term' syntax 
and metadata =
  | Meta_pattern of (term' syntax Prims.list * (term' syntax * arg_qualifier
  FStar_Pervasives_Native.option) Prims.list Prims.list) 
  | Meta_named of FStar_Ident.lident 
  | Meta_labeled of (Prims.string * FStar_Range.range * Prims.bool) 
  | Meta_desugared of meta_source_info 
  | Meta_monadic of (monad_name * term' syntax) 
  | Meta_monadic_lift of (monad_name * monad_name * term' syntax) 
and meta_source_info =
  | Sequence 
  | Primop 
  | Masked_effect 
  | Meta_smt_pat 
and fv_qual =
  | Data_ctor 
  | Record_projector of (FStar_Ident.lident * FStar_Ident.ident) 
  | Record_ctor of (FStar_Ident.lident * FStar_Ident.ident Prims.list) 
and subst_elt =
  | DB of (Prims.int * bv) 
  | NM of (bv * Prims.int) 
  | NT of (bv * term' syntax) 
  | UN of (Prims.int * universe) 
  | UD of (univ_name * Prims.int) 
and 'a syntax = {
  n: 'a ;
  pos: FStar_Range.range ;
  vars: free_vars memo }
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
  blob: FStar_Dyn.dyn ;
  lkind: lazy_kind ;
  ltyp: term' syntax ;
  rng: FStar_Range.range }
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
  | Lazy_embedding of (emb_typ * term' syntax FStar_Thunk.t) 
and binding =
  | Binding_var of bv 
  | Binding_lid of (FStar_Ident.lident * (univ_name Prims.list * term'
  syntax)) 
  | Binding_univ of univ_name 
and arg_qualifier =
  | Implicit of Prims.bool 
  | Meta of arg_qualifier_meta_t 
  | Equality 
and arg_qualifier_meta_t =
  | Arg_qualifier_meta_tac of term' syntax 
  | Arg_qualifier_meta_attr of term' syntax 
let (uu___is_Tm_bvar : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_bvar _0 -> true | uu____1503 -> false
let (__proj__Tm_bvar__item___0 : term' -> bv) =
  fun projectee -> match projectee with | Tm_bvar _0 -> _0
let (uu___is_Tm_name : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_name _0 -> true | uu____1516 -> false
let (__proj__Tm_name__item___0 : term' -> bv) =
  fun projectee -> match projectee with | Tm_name _0 -> _0
let (uu___is_Tm_fvar : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_fvar _0 -> true | uu____1529 -> false
let (__proj__Tm_fvar__item___0 : term' -> fv) =
  fun projectee -> match projectee with | Tm_fvar _0 -> _0
let (uu___is_Tm_uinst : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_uinst _0 -> true | uu____1548 -> false
let (__proj__Tm_uinst__item___0 : term' -> (term' syntax * universes)) =
  fun projectee -> match projectee with | Tm_uinst _0 -> _0
let (uu___is_Tm_constant : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_constant _0 -> true | uu____1579 -> false
let (__proj__Tm_constant__item___0 : term' -> sconst) =
  fun projectee -> match projectee with | Tm_constant _0 -> _0
let (uu___is_Tm_type : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_type _0 -> true | uu____1592 -> false
let (__proj__Tm_type__item___0 : term' -> universe) =
  fun projectee -> match projectee with | Tm_type _0 -> _0
let (uu___is_Tm_abs : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_abs _0 -> true | uu____1623 -> false
let (__proj__Tm_abs__item___0 :
  term' ->
    ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * term'
      syntax * residual_comp FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tm_abs _0 -> _0
let (uu___is_Tm_arrow : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_arrow _0 -> true | uu____1704 -> false
let (__proj__Tm_arrow__item___0 :
  term' ->
    ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * comp'
      syntax))
  = fun projectee -> match projectee with | Tm_arrow _0 -> _0
let (uu___is_Tm_refine : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_refine _0 -> true | uu____1765 -> false
let (__proj__Tm_refine__item___0 : term' -> (bv * term' syntax)) =
  fun projectee -> match projectee with | Tm_refine _0 -> _0
let (uu___is_Tm_app : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_app _0 -> true | uu____1812 -> false
let (__proj__Tm_app__item___0 :
  term' ->
    (term' syntax * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee -> match projectee with | Tm_app _0 -> _0
let (uu___is_Tm_match : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_match _0 -> true | uu____1895 -> false
let (__proj__Tm_match__item___0 :
  term' ->
    (term' syntax * (pat' withinfo_t * term' syntax
      FStar_Pervasives_Native.option * term' syntax) Prims.list))
  = fun projectee -> match projectee with | Tm_match _0 -> _0
let (uu___is_Tm_ascribed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_ascribed _0 -> true | uu____2000 -> false
let (__proj__Tm_ascribed__item___0 :
  term' ->
    (term' syntax * ((term' syntax, comp' syntax) FStar_Util.either * term'
      syntax FStar_Pervasives_Native.option) * FStar_Ident.lident
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tm_ascribed _0 -> _0
let (uu___is_Tm_let : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_let _0 -> true | uu____2103 -> false
let (__proj__Tm_let__item___0 :
  term' -> ((Prims.bool * letbinding Prims.list) * term' syntax)) =
  fun projectee -> match projectee with | Tm_let _0 -> _0
let (uu___is_Tm_uvar : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_uvar _0 -> true | uu____2164 -> false
let (__proj__Tm_uvar__item___0 :
  term' ->
    (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range)))
  = fun projectee -> match projectee with | Tm_uvar _0 -> _0
let (uu___is_Tm_delayed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_delayed _0 -> true | uu____2227 -> false
let (__proj__Tm_delayed__item___0 :
  term' ->
    (term' syntax * (subst_elt Prims.list Prims.list * maybe_set_use_range)))
  = fun projectee -> match projectee with | Tm_delayed _0 -> _0
let (uu___is_Tm_meta : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_meta _0 -> true | uu____2288 -> false
let (__proj__Tm_meta__item___0 : term' -> (term' syntax * metadata)) =
  fun projectee -> match projectee with | Tm_meta _0 -> _0
let (uu___is_Tm_lazy : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_lazy _0 -> true | uu____2319 -> false
let (__proj__Tm_lazy__item___0 : term' -> lazyinfo) =
  fun projectee -> match projectee with | Tm_lazy _0 -> _0
let (uu___is_Tm_quoted : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_quoted _0 -> true | uu____2338 -> false
let (__proj__Tm_quoted__item___0 : term' -> (term' syntax * quoteinfo)) =
  fun projectee -> match projectee with | Tm_quoted _0 -> _0
let (uu___is_Tm_unknown : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tm_unknown -> true | uu____2368 -> false
let (__proj__Mkctx_uvar__item__ctx_uvar_head :
  ctx_uvar ->
    (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
      version * FStar_Range.range))
  =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_head
let (__proj__Mkctx_uvar__item__ctx_uvar_gamma :
  ctx_uvar -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_gamma
let (__proj__Mkctx_uvar__item__ctx_uvar_binders :
  ctx_uvar -> (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_binders
let (__proj__Mkctx_uvar__item__ctx_uvar_typ : ctx_uvar -> term' syntax) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_typ
let (__proj__Mkctx_uvar__item__ctx_uvar_reason : ctx_uvar -> Prims.string) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_reason
let (__proj__Mkctx_uvar__item__ctx_uvar_should_check :
  ctx_uvar -> should_check_uvar) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_should_check
let (__proj__Mkctx_uvar__item__ctx_uvar_range :
  ctx_uvar -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_range
let (__proj__Mkctx_uvar__item__ctx_uvar_meta :
  ctx_uvar -> ctx_uvar_meta_t FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_meta
let (uu___is_Ctx_uvar_meta_tac : ctx_uvar_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Ctx_uvar_meta_tac _0 -> true | uu____2745 -> false
let (__proj__Ctx_uvar_meta_tac__item___0 :
  ctx_uvar_meta_t -> (FStar_Dyn.dyn * term' syntax)) =
  fun projectee -> match projectee with | Ctx_uvar_meta_tac _0 -> _0
let (uu___is_Ctx_uvar_meta_attr : ctx_uvar_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Ctx_uvar_meta_attr _0 -> true
    | uu____2778 -> false
let (__proj__Ctx_uvar_meta_attr__item___0 : ctx_uvar_meta_t -> term' syntax)
  = fun projectee -> match projectee with | Ctx_uvar_meta_attr _0 -> _0
let (uu___is_Pat_constant : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_constant _0 -> true | uu____2797 -> false
let (__proj__Pat_constant__item___0 : pat' -> sconst) =
  fun projectee -> match projectee with | Pat_constant _0 -> _0
let (uu___is_Pat_cons : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_cons _0 -> true | uu____2822 -> false
let (__proj__Pat_cons__item___0 :
  pat' -> (fv * (pat' withinfo_t * Prims.bool) Prims.list)) =
  fun projectee -> match projectee with | Pat_cons _0 -> _0
let (uu___is_Pat_var : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_var _0 -> true | uu____2871 -> false
let (__proj__Pat_var__item___0 : pat' -> bv) =
  fun projectee -> match projectee with | Pat_var _0 -> _0
let (uu___is_Pat_wild : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_wild _0 -> true | uu____2884 -> false
let (__proj__Pat_wild__item___0 : pat' -> bv) =
  fun projectee -> match projectee with | Pat_wild _0 -> _0
let (uu___is_Pat_dot_term : pat' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_dot_term _0 -> true | uu____2903 -> false
let (__proj__Pat_dot_term__item___0 : pat' -> (bv * term' syntax)) =
  fun projectee -> match projectee with | Pat_dot_term _0 -> _0
let (__proj__Mkletbinding__item__lbname :
  letbinding -> (bv, fv) FStar_Util.either) =
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
let (__proj__Mkletbinding__item__lbpos : letbinding -> FStar_Range.range) =
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
  fun projectee ->
    match projectee with | Total _0 -> true | uu____3346 -> false
let (__proj__Total__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Total _0 -> _0
let (uu___is_GTotal : comp' -> Prims.bool) =
  fun projectee ->
    match projectee with | GTotal _0 -> true | uu____3391 -> false
let (__proj__GTotal__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | GTotal _0 -> _0
let (uu___is_Comp : comp' -> Prims.bool) =
  fun projectee ->
    match projectee with | Comp _0 -> true | uu____3428 -> false
let (__proj__Comp__item___0 : comp' -> comp_typ) =
  fun projectee -> match projectee with | Comp _0 -> _0
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee -> match projectee with | TOTAL -> true | uu____3440 -> false
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | MLEFFECT -> true | uu____3446 -> false
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee -> match projectee with | LEMMA -> true | uu____3452 -> false
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | RETURN -> true | uu____3458 -> false
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | PARTIAL_RETURN -> true | uu____3464 -> false
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SOMETRIVIAL -> true | uu____3470 -> false
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TRIVIAL_POSTCONDITION -> true
    | uu____3476 -> false
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOULD_NOT_INLINE -> true | uu____3482 -> false
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee -> match projectee with | CPS -> true | uu____3488 -> false
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES _0 -> true | uu____3497 -> false
let (__proj__DECREASES__item___0 : cflag -> term' syntax) =
  fun projectee -> match projectee with | DECREASES _0 -> _0
let (uu___is_Meta_pattern : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_pattern _0 -> true | uu____3536 -> false
let (__proj__Meta_pattern__item___0 :
  metadata ->
    (term' syntax Prims.list * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list Prims.list))
  = fun projectee -> match projectee with | Meta_pattern _0 -> _0
let (uu___is_Meta_named : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_named _0 -> true | uu____3609 -> false
let (__proj__Meta_named__item___0 : metadata -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Meta_named _0 -> _0
let (uu___is_Meta_labeled : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_labeled _0 -> true | uu____3628 -> false
let (__proj__Meta_labeled__item___0 :
  metadata -> (Prims.string * FStar_Range.range * Prims.bool)) =
  fun projectee -> match projectee with | Meta_labeled _0 -> _0
let (uu___is_Meta_desugared : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_desugared _0 -> true | uu____3659 -> false
let (__proj__Meta_desugared__item___0 : metadata -> meta_source_info) =
  fun projectee -> match projectee with | Meta_desugared _0 -> _0
let (uu___is_Meta_monadic : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_monadic _0 -> true | uu____3678 -> false
let (__proj__Meta_monadic__item___0 :
  metadata -> (monad_name * term' syntax)) =
  fun projectee -> match projectee with | Meta_monadic _0 -> _0
let (uu___is_Meta_monadic_lift : metadata -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_monadic_lift _0 -> true | uu____3717 -> false
let (__proj__Meta_monadic_lift__item___0 :
  metadata -> (monad_name * monad_name * term' syntax)) =
  fun projectee -> match projectee with | Meta_monadic_lift _0 -> _0
let (uu___is_Sequence : meta_source_info -> Prims.bool) =
  fun projectee ->
    match projectee with | Sequence -> true | uu____3753 -> false
let (uu___is_Primop : meta_source_info -> Prims.bool) =
  fun projectee ->
    match projectee with | Primop -> true | uu____3759 -> false
let (uu___is_Masked_effect : meta_source_info -> Prims.bool) =
  fun projectee ->
    match projectee with | Masked_effect -> true | uu____3765 -> false
let (uu___is_Meta_smt_pat : meta_source_info -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta_smt_pat -> true | uu____3771 -> false
let (uu___is_Data_ctor : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Data_ctor -> true | uu____3777 -> false
let (uu___is_Record_projector : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_projector _0 -> true | uu____3788 -> false
let (__proj__Record_projector__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Record_projector _0 -> _0
let (uu___is_Record_ctor : fv_qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_ctor _0 -> true | uu____3819 -> false
let (__proj__Record_ctor__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident Prims.list)) =
  fun projectee -> match projectee with | Record_ctor _0 -> _0
let (uu___is_DB : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | DB _0 -> true | uu____3854 -> false
let (__proj__DB__item___0 : subst_elt -> (Prims.int * bv)) =
  fun projectee -> match projectee with | DB _0 -> _0
let (uu___is_NM : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | NM _0 -> true | uu____3883 -> false
let (__proj__NM__item___0 : subst_elt -> (bv * Prims.int)) =
  fun projectee -> match projectee with | NM _0 -> _0
let (uu___is_NT : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | NT _0 -> true | uu____3914 -> false
let (__proj__NT__item___0 : subst_elt -> (bv * term' syntax)) =
  fun projectee -> match projectee with | NT _0 -> _0
let (uu___is_UN : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | UN _0 -> true | uu____3949 -> false
let (__proj__UN__item___0 : subst_elt -> (Prims.int * universe)) =
  fun projectee -> match projectee with | UN _0 -> _0
let (uu___is_UD : subst_elt -> Prims.bool) =
  fun projectee -> match projectee with | UD _0 -> true | uu____3978 -> false
let (__proj__UD__item___0 : subst_elt -> (univ_name * Prims.int)) =
  fun projectee -> match projectee with | UD _0 -> _0
let __proj__Mksyntax__item__n : 'a . 'a syntax -> 'a =
  fun projectee -> match projectee with | { n; pos; vars;_} -> n
let __proj__Mksyntax__item__pos : 'a . 'a syntax -> FStar_Range.range =
  fun projectee -> match projectee with | { n; pos; vars;_} -> pos
let __proj__Mksyntax__item__vars : 'a . 'a syntax -> free_vars memo =
  fun projectee -> match projectee with | { n; pos; vars;_} -> vars
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
let (__proj__Mklazyinfo__item__blob : lazyinfo -> FStar_Dyn.dyn) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> blob
let (__proj__Mklazyinfo__item__lkind : lazyinfo -> lazy_kind) =
  fun projectee ->
    match projectee with | { blob; lkind; ltyp; rng;_} -> lkind
let (__proj__Mklazyinfo__item__ltyp : lazyinfo -> term' syntax) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> ltyp
let (__proj__Mklazyinfo__item__rng : lazyinfo -> FStar_Range.range) =
  fun projectee -> match projectee with | { blob; lkind; ltyp; rng;_} -> rng
let (uu___is_BadLazy : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | BadLazy -> true | uu____4315 -> false
let (uu___is_Lazy_bv : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_bv -> true | uu____4321 -> false
let (uu___is_Lazy_binder : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_binder -> true | uu____4327 -> false
let (uu___is_Lazy_optionstate : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_optionstate -> true | uu____4333 -> false
let (uu___is_Lazy_fvar : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_fvar -> true | uu____4339 -> false
let (uu___is_Lazy_comp : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_comp -> true | uu____4345 -> false
let (uu___is_Lazy_env : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_env -> true | uu____4351 -> false
let (uu___is_Lazy_proofstate : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_proofstate -> true | uu____4357 -> false
let (uu___is_Lazy_goal : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_goal -> true | uu____4363 -> false
let (uu___is_Lazy_sigelt : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_sigelt -> true | uu____4369 -> false
let (uu___is_Lazy_uvar : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_uvar -> true | uu____4375 -> false
let (uu___is_Lazy_embedding : lazy_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy_embedding _0 -> true | uu____4390 -> false
let (__proj__Lazy_embedding__item___0 :
  lazy_kind -> (emb_typ * term' syntax FStar_Thunk.t)) =
  fun projectee -> match projectee with | Lazy_embedding _0 -> _0
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_var _0 -> true | uu____4427 -> false
let (__proj__Binding_var__item___0 : binding -> bv) =
  fun projectee -> match projectee with | Binding_var _0 -> _0
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_lid _0 -> true | uu____4452 -> false
let (__proj__Binding_lid__item___0 :
  binding -> (FStar_Ident.lident * (univ_name Prims.list * term' syntax))) =
  fun projectee -> match projectee with | Binding_lid _0 -> _0
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_univ _0 -> true | uu____4501 -> false
let (__proj__Binding_univ__item___0 : binding -> univ_name) =
  fun projectee -> match projectee with | Binding_univ _0 -> _0
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Implicit _0 -> true | uu____4514 -> false
let (__proj__Implicit__item___0 : arg_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Implicit _0 -> _0
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____4527 -> false
let (__proj__Meta__item___0 : arg_qualifier -> arg_qualifier_meta_t) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Equality -> true | uu____4539 -> false
let (uu___is_Arg_qualifier_meta_tac : arg_qualifier_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Arg_qualifier_meta_tac _0 -> true
    | uu____4548 -> false
let (__proj__Arg_qualifier_meta_tac__item___0 :
  arg_qualifier_meta_t -> term' syntax) =
  fun projectee -> match projectee with | Arg_qualifier_meta_tac _0 -> _0
let (uu___is_Arg_qualifier_meta_attr : arg_qualifier_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Arg_qualifier_meta_attr _0 -> true
    | uu____4569 -> false
let (__proj__Arg_qualifier_meta_attr__item___0 :
  arg_qualifier_meta_t -> term' syntax) =
  fun projectee -> match projectee with | Arg_qualifier_meta_attr _0 -> _0
type subst_ts = (subst_elt Prims.list Prims.list * maybe_set_use_range)
type ctx_uvar_and_subst =
  (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range))
type term = term' syntax
type uvar =
  (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
    version * FStar_Range.range)
type uvars = ctx_uvar FStar_Util.set
type pat = pat' withinfo_t
type branch =
  (pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term'
    syntax)
type comp = comp' syntax
type ascription =
  ((term' syntax, comp' syntax) FStar_Util.either * term' syntax
    FStar_Pervasives_Native.option)
type antiquotations = (bv * term' syntax) Prims.list
type typ = term' syntax
type aqual = arg_qualifier FStar_Pervasives_Native.option
type arg = (term' syntax * arg_qualifier FStar_Pervasives_Native.option)
type args =
  (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list
type binder = (bv * arg_qualifier FStar_Pervasives_Native.option)
type binders = (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list
type lbname = (bv, fv) FStar_Util.either
type letbindings = (Prims.bool * letbinding Prims.list)
type freenames = bv FStar_Util.set
type attribute = term' syntax
type tscheme = (univ_name Prims.list * term' syntax)
type gamma = binding Prims.list
let (lazy_chooser :
  (lazy_kind -> lazyinfo -> term) FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
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
  fun projectee ->
    match projectee with | Assumption -> true | uu____4813 -> false
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | New -> true | uu____4819 -> false
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____4825 -> false
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Unfold_for_unification_and_vcgen -> true
    | uu____4831 -> false
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Visible_default -> true | uu____4837 -> false
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Irreducible -> true | uu____4843 -> false
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Inline_for_extraction -> true
    | uu____4849 -> false
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | NoExtract -> true | uu____4855 -> false
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Noeq -> true | uu____4861 -> false
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Unopteq -> true | uu____4867 -> false
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TotalEffect -> true | uu____4873 -> false
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Logic -> true | uu____4879 -> false
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reifiable -> true | uu____4885 -> false
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflectable _0 -> true | uu____4892 -> false
let (__proj__Reflectable__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Reflectable _0 -> _0
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Discriminator _0 -> true | uu____4905 -> false
let (__proj__Discriminator__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Discriminator _0 -> _0
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu____4922 -> false
let (__proj__Projector__item___0 :
  qualifier -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordType _0 -> true | uu____4955 -> false
let (__proj__RecordType__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordType _0 -> _0
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordConstructor _0 -> true | uu____5000 -> false
let (__proj__RecordConstructor__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordConstructor _0 -> _0
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Action _0 -> true | uu____5037 -> false
let (__proj__Action__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Action _0 -> _0
let (uu___is_ExceptionConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | ExceptionConstructor -> true | uu____5049 -> false
let (uu___is_HasMaskedEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | HasMaskedEffect -> true | uu____5055 -> false
let (uu___is_Effect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Effect -> true | uu____5061 -> false
let (uu___is_OnlyName : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | OnlyName -> true | uu____5067 -> false
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
type sub_eff =
  {
  source: FStar_Ident.lident ;
  target: FStar_Ident.lident ;
  lift_wp: tscheme FStar_Pervasives_Native.option ;
  lift: tscheme FStar_Pervasives_Native.option }
let (__proj__Mksub_eff__item__source : sub_eff -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift;_} -> source
let (__proj__Mksub_eff__item__target : sub_eff -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift;_} -> target
let (__proj__Mksub_eff__item__lift_wp :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift;_} -> lift_wp
let (__proj__Mksub_eff__item__lift :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { source; target; lift_wp; lift;_} -> lift
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
  l_bind: (tscheme * tscheme) ;
  l_subcomp: (tscheme * tscheme) ;
  l_if_then_else: (tscheme * tscheme) }
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
  layered_eff_combinators -> (tscheme * tscheme)) =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else;_} -> l_bind
let (__proj__Mklayered_eff_combinators__item__l_subcomp :
  layered_eff_combinators -> (tscheme * tscheme)) =
  fun projectee ->
    match projectee with
    | { l_repr; l_return; l_bind; l_subcomp; l_if_then_else;_} -> l_subcomp
let (__proj__Mklayered_eff_combinators__item__l_if_then_else :
  layered_eff_combinators -> (tscheme * tscheme)) =
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
    match projectee with | Primitive_eff _0 -> true | uu____5827 -> false
let (__proj__Primitive_eff__item___0 : eff_combinators -> wp_eff_combinators)
  = fun projectee -> match projectee with | Primitive_eff _0 -> _0
let (uu___is_DM4F_eff : eff_combinators -> Prims.bool) =
  fun projectee ->
    match projectee with | DM4F_eff _0 -> true | uu____5840 -> false
let (__proj__DM4F_eff__item___0 : eff_combinators -> wp_eff_combinators) =
  fun projectee -> match projectee with | DM4F_eff _0 -> _0
let (uu___is_Layered_eff : eff_combinators -> Prims.bool) =
  fun projectee ->
    match projectee with | Layered_eff _0 -> true | uu____5853 -> false
let (__proj__Layered_eff__item___0 :
  eff_combinators -> layered_eff_combinators) =
  fun projectee -> match projectee with | Layered_eff _0 -> _0
type eff_decl =
  {
  mname: FStar_Ident.lident ;
  cattributes: cflag Prims.list ;
  univs: univ_names ;
  binders: binders ;
  signature: tscheme ;
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
let (__proj__Mkeff_decl__item__signature : eff_decl -> tscheme) =
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
  FStar_Ident.lident * tscheme * tscheme) 
  | Sig_polymonadic_subcomp of (FStar_Ident.lident * FStar_Ident.lident *
  tscheme * tscheme) 
  | Sig_fail of (Prims.int Prims.list * Prims.bool * sigelt Prims.list) 
and sigelt =
  {
  sigel: sigelt' ;
  sigrng: FStar_Range.range ;
  sigquals: qualifier Prims.list ;
  sigmeta: sig_metadata ;
  sigattrs: attribute Prims.list ;
  sigopts: FStar_Options.optionstate FStar_Pervasives_Native.option }
let (uu___is_Sig_inductive_typ : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_inductive_typ _0 -> true | uu____6351 -> false
let (__proj__Sig_inductive_typ__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident
      Prims.list * FStar_Ident.lident Prims.list))
  = fun projectee -> match projectee with | Sig_inductive_typ _0 -> _0
let (uu___is_Sig_bundle : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_bundle _0 -> true | uu____6420 -> false
let (__proj__Sig_bundle__item___0 :
  sigelt' -> (sigelt Prims.list * FStar_Ident.lident Prims.list)) =
  fun projectee -> match projectee with | Sig_bundle _0 -> _0
let (uu___is_Sig_datacon : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_datacon _0 -> true | uu____6471 -> false
let (__proj__Sig_datacon__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int *
      FStar_Ident.lident Prims.list))
  = fun projectee -> match projectee with | Sig_datacon _0 -> _0
let (uu___is_Sig_declare_typ : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_declare_typ _0 -> true | uu____6532 -> false
let (__proj__Sig_declare_typ__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * typ)) =
  fun projectee -> match projectee with | Sig_declare_typ _0 -> _0
let (uu___is_Sig_let : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_let _0 -> true | uu____6569 -> false
let (__proj__Sig_let__item___0 :
  sigelt' -> (letbindings * FStar_Ident.lident Prims.list)) =
  fun projectee -> match projectee with | Sig_let _0 -> _0
let (uu___is_Sig_assume : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_assume _0 -> true | uu____6606 -> false
let (__proj__Sig_assume__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * formula)) =
  fun projectee -> match projectee with | Sig_assume _0 -> _0
let (uu___is_Sig_new_effect : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_new_effect _0 -> true | uu____6637 -> false
let (__proj__Sig_new_effect__item___0 : sigelt' -> eff_decl) =
  fun projectee -> match projectee with | Sig_new_effect _0 -> _0
let (uu___is_Sig_sub_effect : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_sub_effect _0 -> true | uu____6650 -> false
let (__proj__Sig_sub_effect__item___0 : sigelt' -> sub_eff) =
  fun projectee -> match projectee with | Sig_sub_effect _0 -> _0
let (uu___is_Sig_effect_abbrev : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_effect_abbrev _0 -> true | uu____6675 -> false
let (__proj__Sig_effect_abbrev__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * comp * cflag Prims.list))
  = fun projectee -> match projectee with | Sig_effect_abbrev _0 -> _0
let (uu___is_Sig_pragma : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_pragma _0 -> true | uu____6724 -> false
let (__proj__Sig_pragma__item___0 : sigelt' -> pragma) =
  fun projectee -> match projectee with | Sig_pragma _0 -> _0
let (uu___is_Sig_splice : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_splice _0 -> true | uu____6743 -> false
let (__proj__Sig_splice__item___0 :
  sigelt' -> (FStar_Ident.lident Prims.list * term)) =
  fun projectee -> match projectee with | Sig_splice _0 -> _0
let (uu___is_Sig_polymonadic_bind : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Sig_polymonadic_bind _0 -> true
    | uu____6784 -> false
let (__proj__Sig_polymonadic_bind__item___0 :
  sigelt' ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * tscheme *
      tscheme))
  = fun projectee -> match projectee with | Sig_polymonadic_bind _0 -> _0
let (uu___is_Sig_polymonadic_subcomp : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Sig_polymonadic_subcomp _0 -> true
    | uu____6835 -> false
let (__proj__Sig_polymonadic_subcomp__item___0 :
  sigelt' -> (FStar_Ident.lident * FStar_Ident.lident * tscheme * tscheme)) =
  fun projectee -> match projectee with | Sig_polymonadic_subcomp _0 -> _0
let (uu___is_Sig_fail : sigelt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sig_fail _0 -> true | uu____6882 -> false
let (__proj__Sig_fail__item___0 :
  sigelt' -> (Prims.int Prims.list * Prims.bool * sigelt Prims.list)) =
  fun projectee -> match projectee with | Sig_fail _0 -> _0
let (__proj__Mksigelt__item__sigel : sigelt -> sigelt') =
  fun projectee ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigel
let (__proj__Mksigelt__item__sigrng : sigelt -> FStar_Range.range) =
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
  sigelt -> FStar_Options.optionstate FStar_Pervasives_Native.option) =
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
let (mod_name : modul -> FStar_Ident.lident) = fun m -> m.name
type path = Prims.string Prims.list
type subst_t = subst_elt Prims.list
let (contains_reflectable : qualifier Prims.list -> Prims.bool) =
  fun l ->
    FStar_Util.for_some
      (fun uu___0_7094 ->
         match uu___0_7094 with
         | Reflectable uu____7095 -> true
         | uu____7096 -> false) l
let withinfo : 'a . 'a -> FStar_Range.range -> 'a withinfo_t =
  fun v -> fun r -> { v; p = r }
let withsort : 'a . 'a -> 'a withinfo_t =
  fun v -> withinfo v FStar_Range.dummyRange
let (bv_eq : bv -> bv -> Prims.bool) =
  fun bv1 ->
    fun bv2 ->
      (FStar_Ident.ident_equals bv1.ppname bv2.ppname) &&
        (bv1.index = bv2.index)
let (order_bv : bv -> bv -> Prims.int) =
  fun x ->
    fun y ->
      let i =
        let uu____7149 = FStar_Ident.string_of_id x.ppname in
        let uu____7150 = FStar_Ident.string_of_id y.ppname in
        FStar_String.compare uu____7149 uu____7150 in
      if i = Prims.int_zero then x.index - y.index else i
let (order_ident : FStar_Ident.ident -> FStar_Ident.ident -> Prims.int) =
  fun x ->
    fun y ->
      let uu____7162 = FStar_Ident.string_of_id x in
      let uu____7163 = FStar_Ident.string_of_id y in
      FStar_String.compare uu____7162 uu____7163
let (order_fv : FStar_Ident.lident -> FStar_Ident.lident -> Prims.int) =
  fun x ->
    fun y ->
      let uu____7174 = FStar_Ident.string_of_lid x in
      let uu____7175 = FStar_Ident.string_of_lid y in
      FStar_String.compare uu____7174 uu____7175
let (range_of_lbname : lbname -> FStar_Range.range) =
  fun l ->
    match l with
    | FStar_Util.Inl x -> FStar_Ident.range_of_id x.ppname
    | FStar_Util.Inr fv1 -> FStar_Ident.range_of_lid (fv1.fv_name).v
let (range_of_bv : bv -> FStar_Range.range) =
  fun x -> FStar_Ident.range_of_id x.ppname
let (set_range_of_bv : bv -> FStar_Range.range -> bv) =
  fun x ->
    fun r ->
      let uu___414_7198 = x in
      let uu____7199 = FStar_Ident.set_id_range r x.ppname in
      {
        ppname = uu____7199;
        index = (uu___414_7198.index);
        sort = (uu___414_7198.sort)
      }
let (on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo) =
  fun f ->
    fun qi ->
      let aq =
        FStar_List.map
          (fun uu____7234 ->
             match uu____7234 with
             | (bv1, t) -> let uu____7245 = f t in (bv1, uu____7245))
          qi.antiquotes in
      let uu___422_7246 = qi in
      { qkind = (uu___422_7246.qkind); antiquotes = aq }
let (lookup_aq : bv -> antiquotations -> term FStar_Pervasives_Native.option)
  =
  fun bv1 ->
    fun aq ->
      let uu____7261 =
        FStar_List.tryFind
          (fun uu____7279 ->
             match uu____7279 with | (bv', uu____7287) -> bv_eq bv1 bv') aq in
      match uu____7261 with
      | FStar_Pervasives_Native.Some (uu____7294, e) ->
          FStar_Pervasives_Native.Some e
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let syn :
  'uuuuuu7324 'uuuuuu7325 'uuuuuu7326 .
    'uuuuuu7324 ->
      'uuuuuu7325 ->
        ('uuuuuu7325 -> 'uuuuuu7324 -> 'uuuuuu7326) -> 'uuuuuu7326
  = fun p -> fun k -> fun f -> f k p
let mk_fvs :
  'uuuuuu7356 .
    unit -> 'uuuuuu7356 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____7365 -> FStar_Util.mk_ref FStar_Pervasives_Native.None
let mk_uvs :
  'uuuuuu7372 .
    unit -> 'uuuuuu7372 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____7381 -> FStar_Util.mk_ref FStar_Pervasives_Native.None
let (new_bv_set : unit -> bv FStar_Util.set) =
  fun uu____7390 -> FStar_Util.new_set order_bv
let (new_id_set : unit -> FStar_Ident.ident FStar_Util.set) =
  fun uu____7399 -> FStar_Util.new_set order_ident
let (new_fv_set : unit -> FStar_Ident.lident FStar_Util.set) =
  fun uu____7408 -> FStar_Util.new_set order_fv
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x ->
    fun y ->
      let uu____7421 = FStar_Ident.string_of_id x in
      let uu____7422 = FStar_Ident.string_of_id y in
      FStar_String.compare uu____7421 uu____7422
let (new_universe_names_set : unit -> univ_name FStar_Util.set) =
  fun uu____7429 -> FStar_Util.new_set order_univ_name
let (eq_binding : binding -> binding -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (Binding_var bv1, Binding_var bv2) -> bv_eq bv1 bv2
      | (Binding_lid (lid1, uu____7445), Binding_lid (lid2, uu____7447)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1, Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu____7482 -> false
let (no_names : freenames) = new_bv_set ()
let (no_fvars : FStar_Ident.lident FStar_Util.set) = new_fv_set ()
let (no_universe_names : univ_name FStar_Util.set) =
  new_universe_names_set ()
let (freenames_of_list : bv Prims.list -> freenames) =
  fun l -> FStar_List.fold_right FStar_Util.set_add l no_names
let (list_of_freenames : freenames -> bv Prims.list) =
  fun fvs -> FStar_Util.set_elements fvs
let mk : 'a . 'a -> FStar_Range.range -> 'a syntax =
  fun t ->
    fun r ->
      let uu____7528 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { n = t; pos = r; vars = uu____7528 }
let (bv_to_tm : bv -> term) =
  fun bv1 -> let uu____7538 = range_of_bv bv1 in mk (Tm_bvar bv1) uu____7538
let (bv_to_name : bv -> term) =
  fun bv1 -> let uu____7544 = range_of_bv bv1 in mk (Tm_name bv1) uu____7544
let (binders_to_names : binders -> term Prims.list) =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.map
         (fun uu____7573 ->
            match uu____7573 with | (x, uu____7581) -> bv_to_name x))
let (mk_Tm_app : term -> args -> FStar_Range.range -> term) =
  fun t1 ->
    fun args1 ->
      fun p ->
        match args1 with | [] -> t1 | uu____7603 -> mk (Tm_app (t1, args1)) p
let (mk_Tm_uinst : term -> universes -> term) =
  fun t ->
    fun us ->
      match t.n with
      | Tm_fvar uu____7628 ->
          (match us with | [] -> t | us1 -> mk (Tm_uinst (t, us1)) t.pos)
      | uu____7632 -> failwith "Unexpected universe instantiation"
let (extend_app_n : term -> args -> FStar_Range.range -> term) =
  fun t ->
    fun args' ->
      fun r ->
        match t.n with
        | Tm_app (head, args1) ->
            mk_Tm_app head (FStar_List.append args1 args') r
        | uu____7682 -> mk_Tm_app t args' r
let (extend_app : term -> arg -> FStar_Range.range -> term) =
  fun t -> fun arg1 -> fun r -> extend_app_n t [arg1] r
let (mk_Tm_delayed : (term * subst_ts) -> FStar_Range.range -> term) =
  fun lr -> fun pos -> mk (Tm_delayed lr) pos
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
    attribute Prims.list * FStar_Range.range) -> letbinding)
  =
  fun uu____7805 ->
    match uu____7805 with
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
      sigrng = FStar_Range.dummyRange;
      sigquals = [];
      sigmeta = default_sigmeta;
      sigattrs = [];
      sigopts = FStar_Pervasives_Native.None
    }
let (mk_subst : subst_t -> subst_t) = fun s -> s
let (extend_subst : subst_elt -> subst_elt Prims.list -> subst_t) =
  fun x -> fun s -> x :: s
let (argpos : arg -> FStar_Range.range) =
  fun x -> (FStar_Pervasives_Native.fst x).pos
let (tun : term) = mk Tm_unknown FStar_Range.dummyRange
let (teff : term) =
  mk (Tm_constant FStar_Const.Const_effect) FStar_Range.dummyRange
let (is_teff : term -> Prims.bool) =
  fun t ->
    match t.n with
    | Tm_constant (FStar_Const.Const_effect) -> true
    | uu____7890 -> false
let (is_type : term -> Prims.bool) =
  fun t -> match t.n with | Tm_type uu____7896 -> true | uu____7897 -> false
let (null_id : FStar_Ident.ident) =
  FStar_Ident.mk_ident ("_", FStar_Range.dummyRange)
let (null_bv : term -> bv) =
  fun k -> { ppname = null_id; index = Prims.int_zero; sort = k }
let (mk_binder : bv -> binder) = fun a -> (a, FStar_Pervasives_Native.None)
let (null_binder : term -> binder) =
  fun t ->
    let uu____7915 = null_bv t in (uu____7915, FStar_Pervasives_Native.None)
let (imp_tag : arg_qualifier) = Implicit false
let (iarg : term -> arg) =
  fun t -> (t, (FStar_Pervasives_Native.Some imp_tag))
let (as_arg : term -> arg) = fun t -> (t, FStar_Pervasives_Native.None)
let (is_null_bv : bv -> Prims.bool) =
  fun b ->
    let uu____7941 = FStar_Ident.string_of_id b.ppname in
    let uu____7942 = FStar_Ident.string_of_id null_id in
    uu____7941 = uu____7942
let (is_null_binder : binder -> Prims.bool) =
  fun b -> is_null_bv (FStar_Pervasives_Native.fst b)
let (is_top_level : letbinding Prims.list -> Prims.bool) =
  fun uu___1_7956 ->
    match uu___1_7956 with
    | { lbname = FStar_Util.Inr uu____7959; lbunivs = uu____7960;
        lbtyp = uu____7961; lbeff = uu____7962; lbdef = uu____7963;
        lbattrs = uu____7964; lbpos = uu____7965;_}::uu____7966 -> true
    | uu____7979 -> false
let (freenames_of_binders : binders -> freenames) =
  fun bs ->
    FStar_List.fold_right
      (fun uu____7999 ->
         fun out ->
           match uu____7999 with
           | (x, uu____8012) -> FStar_Util.set_add x out) bs no_names
let (binders_of_list : bv Prims.list -> binders) =
  fun fvs ->
    FStar_All.pipe_right fvs
      (FStar_List.map (fun t -> (t, FStar_Pervasives_Native.None)))
let (binders_of_freenames : freenames -> binders) =
  fun fvs ->
    let uu____8043 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____8043 binders_of_list
let (is_implicit : aqual -> Prims.bool) =
  fun uu___2_8052 ->
    match uu___2_8052 with
    | FStar_Pervasives_Native.Some (Implicit uu____8053) -> true
    | uu____8054 -> false
let (is_implicit_or_meta : aqual -> Prims.bool) =
  fun uu___3_8059 ->
    match uu___3_8059 with
    | FStar_Pervasives_Native.Some (Implicit uu____8060) -> true
    | FStar_Pervasives_Native.Some (Meta uu____8061) -> true
    | uu____8062 -> false
let (as_implicit : Prims.bool -> aqual) =
  fun uu___4_8067 ->
    if uu___4_8067
    then FStar_Pervasives_Native.Some imp_tag
    else FStar_Pervasives_Native.None
let (pat_bvs : pat -> bv Prims.list) =
  fun p ->
    let rec aux b p1 =
      match p1.v with
      | Pat_dot_term uu____8101 -> b
      | Pat_constant uu____8108 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____8111, pats) ->
          FStar_List.fold_left
            (fun b1 ->
               fun uu____8142 ->
                 match uu____8142 with | (p2, uu____8154) -> aux b1 p2) b
            pats in
    let uu____8159 = aux [] p in
    FStar_All.pipe_left FStar_List.rev uu____8159
let (range_of_ropt :
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Range.range) =
  fun uu___5_8172 ->
    match uu___5_8172 with
    | FStar_Pervasives_Native.None -> FStar_Range.dummyRange
    | FStar_Pervasives_Native.Some r -> r
let (gen_bv :
  Prims.string ->
    FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv)
  =
  fun s ->
    fun r ->
      fun t ->
        let id = FStar_Ident.mk_ident (s, (range_of_ropt r)) in
        let uu____8207 = FStar_Ident.next_id () in
        { ppname = id; index = uu____8207; sort = t }
let (new_bv : FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv)
  = fun ropt -> fun t -> gen_bv FStar_Ident.reserved_prefix ropt t
let (freshen_bv : bv -> bv) =
  fun bv1 ->
    let uu____8227 = is_null_bv bv1 in
    if uu____8227
    then
      let uu____8228 =
        let uu____8231 = range_of_bv bv1 in
        FStar_Pervasives_Native.Some uu____8231 in
      new_bv uu____8228 bv1.sort
    else
      (let uu___608_8233 = bv1 in
       let uu____8234 = FStar_Ident.next_id () in
       {
         ppname = (uu___608_8233.ppname);
         index = uu____8234;
         sort = (uu___608_8233.sort)
       })
let (freshen_binder : binder -> binder) =
  fun b ->
    let uu____8240 = b in
    match uu____8240 with
    | (bv1, aq) -> let uu____8247 = freshen_bv bv1 in (uu____8247, aq)
let (new_univ_name :
  FStar_Range.range FStar_Pervasives_Native.option -> univ_name) =
  fun ropt ->
    let id = FStar_Ident.next_id () in
    let uu____8260 =
      let uu____8265 =
        let uu____8266 = FStar_Util.string_of_int id in
        Prims.op_Hat FStar_Ident.reserved_prefix uu____8266 in
      (uu____8265, (range_of_ropt ropt)) in
    FStar_Ident.mk_ident uu____8260
let (lbname_eq :
  (bv, FStar_Ident.lident) FStar_Util.either ->
    (bv, FStar_Ident.lident) FStar_Util.either -> Prims.bool)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (FStar_Util.Inl x, FStar_Util.Inl y) -> bv_eq x y
      | (FStar_Util.Inr l, FStar_Util.Inr m) -> FStar_Ident.lid_equals l m
      | uu____8321 -> false
let (fv_eq : fv -> fv -> Prims.bool) =
  fun fv1 ->
    fun fv2 -> FStar_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
let (fv_eq_lid : fv -> FStar_Ident.lident -> Prims.bool) =
  fun fv1 -> fun lid -> FStar_Ident.lid_equals (fv1.fv_name).v lid
let (set_bv_range : bv -> FStar_Range.range -> bv) =
  fun bv1 ->
    fun r ->
      let uu___635_8364 = bv1 in
      let uu____8365 = FStar_Ident.set_id_range r bv1.ppname in
      {
        ppname = uu____8365;
        index = (uu___635_8364.index);
        sort = (uu___635_8364.sort)
      }
let (lid_as_fv :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> fv)
  =
  fun l ->
    fun dd ->
      fun dq ->
        let uu____8385 =
          let uu____8386 = FStar_Ident.range_of_lid l in
          withinfo l uu____8386 in
        { fv_name = uu____8385; fv_delta = dd; fv_qual = dq }
let (fv_to_tm : fv -> term) =
  fun fv1 ->
    let uu____8392 = FStar_Ident.range_of_lid (fv1.fv_name).v in
    mk (Tm_fvar fv1) uu____8392
let (fvar :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> term)
  =
  fun l ->
    fun dd ->
      fun dq -> let uu____8412 = lid_as_fv l dd dq in fv_to_tm uu____8412
let (lid_of_fv : fv -> FStar_Ident.lid) = fun fv1 -> (fv1.fv_name).v
let (range_of_fv : fv -> FStar_Range.range) =
  fun fv1 ->
    let uu____8423 = lid_of_fv fv1 in FStar_Ident.range_of_lid uu____8423
let (set_range_of_fv : fv -> FStar_Range.range -> fv) =
  fun fv1 ->
    fun r ->
      let uu___648_8434 = fv1 in
      let uu____8435 =
        let uu___650_8436 = fv1.fv_name in
        let uu____8437 =
          let uu____8438 = lid_of_fv fv1 in
          FStar_Ident.set_lid_range uu____8438 r in
        { v = uu____8437; p = (uu___650_8436.p) } in
      {
        fv_name = uu____8435;
        fv_delta = (uu___648_8434.fv_delta);
        fv_qual = (uu___648_8434.fv_qual)
      }
let (has_simple_attribute : term Prims.list -> Prims.string -> Prims.bool) =
  fun l ->
    fun s ->
      FStar_List.existsb
        (fun uu___6_8460 ->
           match uu___6_8460 with
           | { n = Tm_constant (FStar_Const.Const_string (data, uu____8464));
               pos = uu____8465; vars = uu____8466;_} when data = s -> true
           | uu____8469 -> false) l
let rec (eq_pat : pat -> pat -> Prims.bool) =
  fun p1 ->
    fun p2 ->
      match ((p1.v), (p2.v)) with
      | (Pat_constant c1, Pat_constant c2) -> FStar_Const.eq_const c1 c2
      | (Pat_cons (fv1, as1), Pat_cons (fv2, as2)) ->
          let uu____8520 = fv_eq fv1 fv2 in
          if uu____8520
          then
            let uu____8522 = FStar_List.zip as1 as2 in
            FStar_All.pipe_right uu____8522
              (FStar_List.for_all
                 (fun uu____8580 ->
                    match uu____8580 with
                    | ((p11, b1), (p21, b2)) -> (b1 = b2) && (eq_pat p11 p21)))
          else false
      | (Pat_var uu____8606, Pat_var uu____8607) -> true
      | (Pat_wild uu____8608, Pat_wild uu____8609) -> true
      | (Pat_dot_term (bv1, t1), Pat_dot_term (bv2, t2)) -> true
      | (uu____8622, uu____8623) -> false
let (delta_constant : delta_depth) = Delta_constant_at_level Prims.int_zero
let (delta_equational : delta_depth) =
  Delta_equational_at_level Prims.int_zero
let (fvconst : FStar_Ident.lident -> fv) =
  fun l -> lid_as_fv l delta_constant FStar_Pervasives_Native.None
let (tconst : FStar_Ident.lident -> term) =
  fun l ->
    let uu____8634 = let uu____8635 = fvconst l in Tm_fvar uu____8635 in
    mk uu____8634 FStar_Range.dummyRange
let (tabbrev : FStar_Ident.lident -> term) =
  fun l ->
    let uu____8641 =
      let uu____8642 =
        lid_as_fv l (Delta_constant_at_level Prims.int_one)
          FStar_Pervasives_Native.None in
      Tm_fvar uu____8642 in
    mk uu____8641 FStar_Range.dummyRange
let (tdataconstr : FStar_Ident.lident -> term) =
  fun l ->
    let uu____8648 =
      lid_as_fv l delta_constant (FStar_Pervasives_Native.Some Data_ctor) in
    fv_to_tm uu____8648
let (t_unit : term) = tconst FStar_Parser_Const.unit_lid
let (t_bool : term) = tconst FStar_Parser_Const.bool_lid
let (t_int : term) = tconst FStar_Parser_Const.int_lid
let (t_string : term) = tconst FStar_Parser_Const.string_lid
let (t_exn : term) = tconst FStar_Parser_Const.exn_lid
let (t_real : term) = tconst FStar_Parser_Const.real_lid
let (t_float : term) = tconst FStar_Parser_Const.float_lid
let (t_char : term) = tabbrev FStar_Parser_Const.char_lid
let (t_range : term) = tconst FStar_Parser_Const.range_lid
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
      let uu____8659 =
        let uu____8660 = tabbrev FStar_Parser_Const.tac_lid in
        mk_Tm_uinst uu____8660 [U_zero; U_zero] in
      let uu____8661 =
        let uu____8662 = as_arg a in
        let uu____8671 = let uu____8682 = as_arg b in [uu____8682] in
        uu____8662 :: uu____8671 in
      mk_Tm_app uu____8659 uu____8661 FStar_Range.dummyRange
let (t_tactic_of : term -> term) =
  fun t ->
    let uu____8720 =
      let uu____8721 = tabbrev FStar_Parser_Const.tactic_lid in
      mk_Tm_uinst uu____8721 [U_zero] in
    let uu____8722 = let uu____8723 = as_arg t in [uu____8723] in
    mk_Tm_app uu____8720 uu____8722 FStar_Range.dummyRange
let (t_tactic_unit : term) = t_tactic_of t_unit
let (t_list_of : term -> term) =
  fun t ->
    let uu____8753 =
      let uu____8754 = tabbrev FStar_Parser_Const.list_lid in
      mk_Tm_uinst uu____8754 [U_zero] in
    let uu____8755 = let uu____8756 = as_arg t in [uu____8756] in
    mk_Tm_app uu____8753 uu____8755 FStar_Range.dummyRange
let (t_option_of : term -> term) =
  fun t ->
    let uu____8786 =
      let uu____8787 = tabbrev FStar_Parser_Const.option_lid in
      mk_Tm_uinst uu____8787 [U_zero] in
    let uu____8788 = let uu____8789 = as_arg t in [uu____8789] in
    mk_Tm_app uu____8786 uu____8788 FStar_Range.dummyRange
let (t_tuple2_of : term -> term -> term) =
  fun t1 ->
    fun t2 ->
      let uu____8824 =
        let uu____8825 = tabbrev FStar_Parser_Const.lid_tuple2 in
        mk_Tm_uinst uu____8825 [U_zero; U_zero] in
      let uu____8826 =
        let uu____8827 = as_arg t1 in
        let uu____8836 = let uu____8847 = as_arg t2 in [uu____8847] in
        uu____8827 :: uu____8836 in
      mk_Tm_app uu____8824 uu____8826 FStar_Range.dummyRange
let (t_either_of : term -> term -> term) =
  fun t1 ->
    fun t2 ->
      let uu____8890 =
        let uu____8891 = tabbrev FStar_Parser_Const.either_lid in
        mk_Tm_uinst uu____8891 [U_zero; U_zero] in
      let uu____8892 =
        let uu____8893 = as_arg t1 in
        let uu____8902 = let uu____8913 = as_arg t2 in [uu____8913] in
        uu____8893 :: uu____8902 in
      mk_Tm_app uu____8890 uu____8892 FStar_Range.dummyRange
let (unit_const_with_range : FStar_Range.range -> term) =
  fun r -> mk (Tm_constant FStar_Const.Const_unit) r
let (unit_const : term) = unit_const_with_range FStar_Range.dummyRange