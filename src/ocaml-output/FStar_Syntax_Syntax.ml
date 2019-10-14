open Prims
type 'a withinfo_t = {
  v: 'a ;
  p: FStar_Range.range }[@@deriving yojson,show,yojson,show]
let __proj__Mkwithinfo_t__item__v : 'a . 'a withinfo_t -> 'a =
  fun projectee  -> match projectee with | { v = v1; p;_} -> v1 
let __proj__Mkwithinfo_t__item__p : 'a . 'a withinfo_t -> FStar_Range.range =
  fun projectee  -> match projectee with | { v = v1; p;_} -> p 
type var = FStar_Ident.lident withinfo_t[@@deriving yojson,show]
type sconst = FStar_Const.sconst[@@deriving yojson,show]
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | LightOff [@@deriving yojson,show,yojson,show]
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____176 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____201 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____232 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____259 -> false
  
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | RestartSolver  -> true | uu____270 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____281 -> false
  
type 'a memo =
  (('a FStar_Pervasives_Native.option FStar_ST.ref)[@printer
                                                     fun fmt  ->
                                                       fun _  ->
                                                         Format.pp_print_string
                                                           fmt "None"])
[@@deriving yojson,show]
type emb_typ =
  | ET_abstract 
  | ET_fun of (emb_typ * emb_typ) 
  | ET_app of (Prims.string * emb_typ Prims.list) 
let (uu___is_ET_abstract : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_abstract  -> true | uu____321 -> false
  
let (uu___is_ET_fun : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_fun _0 -> true | uu____337 -> false
  
let (__proj__ET_fun__item___0 : emb_typ -> (emb_typ * emb_typ)) =
  fun projectee  -> match projectee with | ET_fun _0 -> _0 
let (uu___is_ET_app : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_app _0 -> true | uu____375 -> false
  
let (__proj__ET_app__item___0 :
  emb_typ -> (Prims.string * emb_typ Prims.list)) =
  fun projectee  -> match projectee with | ET_app _0 -> _0 
type version = {
  major: Prims.int ;
  minor: Prims.int }[@@deriving yojson,show,yojson,show]
let (__proj__Mkversion__item__major : version -> Prims.int) =
  fun projectee  -> match projectee with | { major; minor;_} -> major 
let (__proj__Mkversion__item__minor : version -> Prims.int) =
  fun projectee  -> match projectee with | { major; minor;_} -> minor 
type universe =
  | U_zero 
  | U_succ of universe 
  | U_max of universe Prims.list 
  | U_bvar of Prims.int 
  | U_name of FStar_Ident.ident 
  | U_unif of (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar
  * version) 
  | U_unknown [@@deriving yojson,show,yojson,show]
let (uu___is_U_zero : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_zero  -> true | uu____486 -> false
  
let (uu___is_U_succ : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_succ _0 -> true | uu____498 -> false
  
let (__proj__U_succ__item___0 : universe -> universe) =
  fun projectee  -> match projectee with | U_succ _0 -> _0 
let (uu___is_U_max : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_max _0 -> true | uu____519 -> false
  
let (__proj__U_max__item___0 : universe -> universe Prims.list) =
  fun projectee  -> match projectee with | U_max _0 -> _0 
let (uu___is_U_bvar : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_bvar _0 -> true | uu____545 -> false
  
let (__proj__U_bvar__item___0 : universe -> Prims.int) =
  fun projectee  -> match projectee with | U_bvar _0 -> _0 
let (uu___is_U_name : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_name _0 -> true | uu____567 -> false
  
let (__proj__U_name__item___0 : universe -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | U_name _0 -> _0 
let (uu___is_U_unif : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_unif _0 -> true | uu____594 -> false
  
let (__proj__U_unif__item___0 :
  universe ->
    (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
      version))
  = fun projectee  -> match projectee with | U_unif _0 -> _0 
let (uu___is_U_unknown : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_unknown  -> true | uu____636 -> false
  
type univ_name = FStar_Ident.ident[@@deriving yojson,show]
type universe_uvar =
  (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version)
[@@deriving yojson,show]
type univ_names = univ_name Prims.list[@@deriving yojson,show]
type universes = universe Prims.list[@@deriving yojson,show]
type monad_name = FStar_Ident.lident[@@deriving yojson,show]
type quote_kind =
  | Quote_static 
  | Quote_dynamic [@@deriving yojson,show,yojson,show]
let (uu___is_Quote_static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote_static  -> true | uu____659 -> false
  
let (uu___is_Quote_dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote_dynamic  -> true | uu____670 -> false
  
type maybe_set_use_range =
  | NoUseRange 
  | SomeUseRange of FStar_Range.range [@@deriving yojson,show,yojson,show]
let (uu___is_NoUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUseRange  -> true | uu____686 -> false
  
let (uu___is_SomeUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee  ->
    match projectee with | SomeUseRange _0 -> true | uu____698 -> false
  
let (__proj__SomeUseRange__item___0 :
  maybe_set_use_range -> FStar_Range.range) =
  fun projectee  -> match projectee with | SomeUseRange _0 -> _0 
type delta_depth =
  | Delta_constant_at_level of Prims.int 
  | Delta_equational_at_level of Prims.int 
  | Delta_abstract of delta_depth [@@deriving yojson,show,yojson,show]
let (uu___is_Delta_constant_at_level : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Delta_constant_at_level _0 -> true
    | uu____735 -> false
  
let (__proj__Delta_constant_at_level__item___0 : delta_depth -> Prims.int) =
  fun projectee  -> match projectee with | Delta_constant_at_level _0 -> _0 
let (uu___is_Delta_equational_at_level : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Delta_equational_at_level _0 -> true
    | uu____758 -> false
  
let (__proj__Delta_equational_at_level__item___0 : delta_depth -> Prims.int)
  =
  fun projectee  -> match projectee with | Delta_equational_at_level _0 -> _0 
let (uu___is_Delta_abstract : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta_abstract _0 -> true | uu____780 -> false
  
let (__proj__Delta_abstract__item___0 : delta_depth -> delta_depth) =
  fun projectee  -> match projectee with | Delta_abstract _0 -> _0 
type should_check_uvar =
  | Allow_unresolved 
  | Allow_untyped 
  | Strict [@@deriving yojson,show,yojson,show]
let (uu___is_Allow_unresolved : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Allow_unresolved  -> true | uu____798 -> false
  
let (uu___is_Allow_untyped : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Allow_untyped  -> true | uu____809 -> false
  
let (uu___is_Strict : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Strict  -> true | uu____820 -> false
  
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
  | Tm_ascribed of (term' syntax * ((term' syntax,comp' syntax)
  FStar_Util.either * term' syntax FStar_Pervasives_Native.option) *
  FStar_Ident.lident FStar_Pervasives_Native.option) 
  | Tm_let of ((Prims.bool * letbinding Prims.list) * term' syntax) 
  | Tm_uvar of (ctx_uvar * (subst_elt Prims.list Prims.list *
  maybe_set_use_range)) 
  | Tm_delayed of ((term' syntax * (subst_elt Prims.list Prims.list *
  maybe_set_use_range)) * term' syntax memo) 
  | Tm_meta of (term' syntax * metadata) 
  | Tm_lazy of lazyinfo 
  | Tm_quoted of (term' syntax * quoteinfo) 
  | Tm_unknown 
and ctx_uvar =
  {
  ctx_uvar_head:
    (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
      version)
    ;
  ctx_uvar_gamma: binding Prims.list ;
  ctx_uvar_binders:
    (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list ;
  ctx_uvar_typ: term' syntax ;
  ctx_uvar_reason: Prims.string ;
  ctx_uvar_should_check: should_check_uvar ;
  ctx_uvar_range: FStar_Range.range ;
  ctx_uvar_meta:
    (FStar_Dyn.dyn * term' syntax) FStar_Pervasives_Native.option }
and pat' =
  | Pat_constant of sconst 
  | Pat_cons of (fv * (pat' withinfo_t * Prims.bool) Prims.list) 
  | Pat_var of bv 
  | Pat_wild of bv 
  | Pat_dot_term of (bv * term' syntax) 
and letbinding =
  {
  lbname: (bv,fv) FStar_Util.either ;
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
  | Lazy_embedding of (emb_typ * term' syntax FStar_Common.thunk) 
and binding =
  | Binding_var of bv 
  | Binding_lid of (FStar_Ident.lident * (univ_name Prims.list * term'
  syntax)) 
  | Binding_univ of univ_name 
and arg_qualifier =
  | Implicit of Prims.bool 
  | Meta of term' syntax 
  | Equality 
let (uu___is_Tm_bvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_bvar _0 -> true | uu____1710 -> false
  
let (__proj__Tm_bvar__item___0 : term' -> bv) =
  fun projectee  -> match projectee with | Tm_bvar _0 -> _0 
let (uu___is_Tm_name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_name _0 -> true | uu____1729 -> false
  
let (__proj__Tm_name__item___0 : term' -> bv) =
  fun projectee  -> match projectee with | Tm_name _0 -> _0 
let (uu___is_Tm_fvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_fvar _0 -> true | uu____1748 -> false
  
let (__proj__Tm_fvar__item___0 : term' -> fv) =
  fun projectee  -> match projectee with | Tm_fvar _0 -> _0 
let (uu___is_Tm_uinst : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_uinst _0 -> true | uu____1773 -> false
  
let (__proj__Tm_uinst__item___0 : term' -> (term' syntax * universes)) =
  fun projectee  -> match projectee with | Tm_uinst _0 -> _0 
let (uu___is_Tm_constant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_constant _0 -> true | uu____1810 -> false
  
let (__proj__Tm_constant__item___0 : term' -> sconst) =
  fun projectee  -> match projectee with | Tm_constant _0 -> _0 
let (uu___is_Tm_type : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_type _0 -> true | uu____1829 -> false
  
let (__proj__Tm_type__item___0 : term' -> universe) =
  fun projectee  -> match projectee with | Tm_type _0 -> _0 
let (uu___is_Tm_abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_abs _0 -> true | uu____1866 -> false
  
let (__proj__Tm_abs__item___0 :
  term' ->
    ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * term'
      syntax * residual_comp FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tm_abs _0 -> _0 
let (uu___is_Tm_arrow : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_arrow _0 -> true | uu____1953 -> false
  
let (__proj__Tm_arrow__item___0 :
  term' ->
    ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * comp'
      syntax))
  = fun projectee  -> match projectee with | Tm_arrow _0 -> _0 
let (uu___is_Tm_refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_refine _0 -> true | uu____2020 -> false
  
let (__proj__Tm_refine__item___0 : term' -> (bv * term' syntax)) =
  fun projectee  -> match projectee with | Tm_refine _0 -> _0 
let (uu___is_Tm_app : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_app _0 -> true | uu____2073 -> false
  
let (__proj__Tm_app__item___0 :
  term' ->
    (term' syntax * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee  -> match projectee with | Tm_app _0 -> _0 
let (uu___is_Tm_match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_match _0 -> true | uu____2162 -> false
  
let (__proj__Tm_match__item___0 :
  term' ->
    (term' syntax * (pat' withinfo_t * term' syntax
      FStar_Pervasives_Native.option * term' syntax) Prims.list))
  = fun projectee  -> match projectee with | Tm_match _0 -> _0 
let (uu___is_Tm_ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_ascribed _0 -> true | uu____2273 -> false
  
let (__proj__Tm_ascribed__item___0 :
  term' ->
    (term' syntax * ((term' syntax,comp' syntax) FStar_Util.either * term'
      syntax FStar_Pervasives_Native.option) * FStar_Ident.lident
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tm_ascribed _0 -> _0 
let (uu___is_Tm_let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_let _0 -> true | uu____2383 -> false
  
let (__proj__Tm_let__item___0 :
  term' -> ((Prims.bool * letbinding Prims.list) * term' syntax)) =
  fun projectee  -> match projectee with | Tm_let _0 -> _0 
let (uu___is_Tm_uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_uvar _0 -> true | uu____2453 -> false
  
let (__proj__Tm_uvar__item___0 :
  term' ->
    (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range)))
  = fun projectee  -> match projectee with | Tm_uvar _0 -> _0 
let (uu___is_Tm_delayed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_delayed _0 -> true | uu____2530 -> false
  
let (__proj__Tm_delayed__item___0 :
  term' ->
    ((term' syntax * (subst_elt Prims.list Prims.list * maybe_set_use_range))
      * term' syntax memo))
  = fun projectee  -> match projectee with | Tm_delayed _0 -> _0 
let (uu___is_Tm_meta : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_meta _0 -> true | uu____2621 -> false
  
let (__proj__Tm_meta__item___0 : term' -> (term' syntax * metadata)) =
  fun projectee  -> match projectee with | Tm_meta _0 -> _0 
let (uu___is_Tm_lazy : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_lazy _0 -> true | uu____2658 -> false
  
let (__proj__Tm_lazy__item___0 : term' -> lazyinfo) =
  fun projectee  -> match projectee with | Tm_lazy _0 -> _0 
let (uu___is_Tm_quoted : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_quoted _0 -> true | uu____2683 -> false
  
let (__proj__Tm_quoted__item___0 : term' -> (term' syntax * quoteinfo)) =
  fun projectee  -> match projectee with | Tm_quoted _0 -> _0 
let (uu___is_Tm_unknown : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_unknown  -> true | uu____2719 -> false
  
let (__proj__Mkctx_uvar__item__ctx_uvar_head :
  ctx_uvar ->
    (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
      version))
  =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_head
  
let (__proj__Mkctx_uvar__item__ctx_uvar_gamma :
  ctx_uvar -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_gamma
  
let (__proj__Mkctx_uvar__item__ctx_uvar_binders :
  ctx_uvar -> (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_binders
  
let (__proj__Mkctx_uvar__item__ctx_uvar_typ : ctx_uvar -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_typ
  
let (__proj__Mkctx_uvar__item__ctx_uvar_reason : ctx_uvar -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_reason
  
let (__proj__Mkctx_uvar__item__ctx_uvar_should_check :
  ctx_uvar -> should_check_uvar) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_should_check
  
let (__proj__Mkctx_uvar__item__ctx_uvar_range :
  ctx_uvar -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_range
  
let (__proj__Mkctx_uvar__item__ctx_uvar_meta :
  ctx_uvar -> (FStar_Dyn.dyn * term' syntax) FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head; ctx_uvar_gamma; ctx_uvar_binders; ctx_uvar_typ;
        ctx_uvar_reason; ctx_uvar_should_check; ctx_uvar_range;
        ctx_uvar_meta;_} -> ctx_uvar_meta
  
let (uu___is_Pat_constant : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_constant _0 -> true | uu____3153 -> false
  
let (__proj__Pat_constant__item___0 : pat' -> sconst) =
  fun projectee  -> match projectee with | Pat_constant _0 -> _0 
let (uu___is_Pat_cons : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_cons _0 -> true | uu____3185 -> false
  
let (__proj__Pat_cons__item___0 :
  pat' -> (fv * (pat' withinfo_t * Prims.bool) Prims.list)) =
  fun projectee  -> match projectee with | Pat_cons _0 -> _0 
let (uu___is_Pat_var : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_var _0 -> true | uu____3243 -> false
  
let (__proj__Pat_var__item___0 : pat' -> bv) =
  fun projectee  -> match projectee with | Pat_var _0 -> _0 
let (uu___is_Pat_wild : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_wild _0 -> true | uu____3262 -> false
  
let (__proj__Pat_wild__item___0 : pat' -> bv) =
  fun projectee  -> match projectee with | Pat_wild _0 -> _0 
let (uu___is_Pat_dot_term : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_dot_term _0 -> true | uu____3287 -> false
  
let (__proj__Pat_dot_term__item___0 : pat' -> (bv * term' syntax)) =
  fun projectee  -> match projectee with | Pat_dot_term _0 -> _0 
let (__proj__Mkletbinding__item__lbname :
  letbinding -> (bv,fv) FStar_Util.either) =
  fun projectee  ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbname
  
let (__proj__Mkletbinding__item__lbunivs :
  letbinding -> univ_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbunivs
  
let (__proj__Mkletbinding__item__lbtyp : letbinding -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbtyp
  
let (__proj__Mkletbinding__item__lbeff : letbinding -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbeff
  
let (__proj__Mkletbinding__item__lbdef : letbinding -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbdef
  
let (__proj__Mkletbinding__item__lbattrs :
  letbinding -> term' syntax Prims.list) =
  fun projectee  ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbattrs
  
let (__proj__Mkletbinding__item__lbpos : letbinding -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos;_} -> lbpos
  
let (__proj__Mkquoteinfo__item__qkind : quoteinfo -> quote_kind) =
  fun projectee  -> match projectee with | { qkind; antiquotes;_} -> qkind 
let (__proj__Mkquoteinfo__item__antiquotes :
  quoteinfo -> (bv * term' syntax) Prims.list) =
  fun projectee  ->
    match projectee with | { qkind; antiquotes;_} -> antiquotes
  
let (__proj__Mkcomp_typ__item__comp_univs : comp_typ -> universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ ->
    (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_args
  
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} -> flags
  
let (uu___is_Total : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Total _0 -> true | uu____3750 -> false
  
let (__proj__Total__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Total _0 -> _0 
let (uu___is_GTotal : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTotal _0 -> true | uu____3801 -> false
  
let (__proj__GTotal__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | GTotal _0 -> _0 
let (uu___is_Comp : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____3844 -> false
  
let (__proj__Comp__item___0 : comp' -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____3862 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____3873 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____3884 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____3895 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____3906 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____3917 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____3928 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____3939 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____3950 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____3964 -> false
  
let (__proj__DECREASES__item___0 : cflag -> term' syntax) =
  fun projectee  -> match projectee with | DECREASES _0 -> _0 
let (uu___is_Meta_pattern : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_pattern _0 -> true | uu____4009 -> false
  
let (__proj__Meta_pattern__item___0 :
  metadata ->
    (term' syntax Prims.list * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list Prims.list))
  = fun projectee  -> match projectee with | Meta_pattern _0 -> _0 
let (uu___is_Meta_named : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_named _0 -> true | uu____4088 -> false
  
let (__proj__Meta_named__item___0 : metadata -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Meta_named _0 -> _0 
let (uu___is_Meta_labeled : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_labeled _0 -> true | uu____4115 -> false
  
let (__proj__Meta_labeled__item___0 :
  metadata -> (Prims.string * FStar_Range.range * Prims.bool)) =
  fun projectee  -> match projectee with | Meta_labeled _0 -> _0 
let (uu___is_Meta_desugared : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_desugared _0 -> true | uu____4158 -> false
  
let (__proj__Meta_desugared__item___0 : metadata -> meta_source_info) =
  fun projectee  -> match projectee with | Meta_desugared _0 -> _0 
let (uu___is_Meta_monadic : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_monadic _0 -> true | uu____4183 -> false
  
let (__proj__Meta_monadic__item___0 :
  metadata -> (monad_name * term' syntax)) =
  fun projectee  -> match projectee with | Meta_monadic _0 -> _0 
let (uu___is_Meta_monadic_lift : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_monadic_lift _0 -> true | uu____4228 -> false
  
let (__proj__Meta_monadic_lift__item___0 :
  metadata -> (monad_name * monad_name * term' syntax)) =
  fun projectee  -> match projectee with | Meta_monadic_lift _0 -> _0 
let (uu___is_Sequence : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sequence  -> true | uu____4270 -> false
  
let (uu___is_Primop : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primop  -> true | uu____4281 -> false
  
let (uu___is_Masked_effect : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Masked_effect  -> true | uu____4292 -> false
  
let (uu___is_Meta_smt_pat : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_smt_pat  -> true | uu____4303 -> false
  
let (uu___is_Data_ctor : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Data_ctor  -> true | uu____4314 -> false
  
let (uu___is_Record_projector : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_projector _0 -> true | uu____4330 -> false
  
let (__proj__Record_projector__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Record_projector _0 -> _0 
let (uu___is_Record_ctor : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_ctor _0 -> true | uu____4367 -> false
  
let (__proj__Record_ctor__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident Prims.list)) =
  fun projectee  -> match projectee with | Record_ctor _0 -> _0 
let (uu___is_DB : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | DB _0 -> true | uu____4409 -> false
  
let (__proj__DB__item___0 : subst_elt -> (Prims.int * bv)) =
  fun projectee  -> match projectee with | DB _0 -> _0 
let (uu___is_NM : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | NM _0 -> true | uu____4448 -> false
  
let (__proj__NM__item___0 : subst_elt -> (bv * Prims.int)) =
  fun projectee  -> match projectee with | NM _0 -> _0 
let (uu___is_NT : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | NT _0 -> true | uu____4488 -> false
  
let (__proj__NT__item___0 : subst_elt -> (bv * term' syntax)) =
  fun projectee  -> match projectee with | NT _0 -> _0 
let (uu___is_UN : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UN _0 -> true | uu____4530 -> false
  
let (__proj__UN__item___0 : subst_elt -> (Prims.int * universe)) =
  fun projectee  -> match projectee with | UN _0 -> _0 
let (uu___is_UD : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UD _0 -> true | uu____4569 -> false
  
let (__proj__UD__item___0 : subst_elt -> (univ_name * Prims.int)) =
  fun projectee  -> match projectee with | UD _0 -> _0 
let __proj__Mksyntax__item__n : 'a . 'a syntax -> 'a =
  fun projectee  -> match projectee with | { n = n1; pos; vars;_} -> n1 
let __proj__Mksyntax__item__pos : 'a . 'a syntax -> FStar_Range.range =
  fun projectee  -> match projectee with | { n = n1; pos; vars;_} -> pos 
let __proj__Mksyntax__item__vars : 'a . 'a syntax -> free_vars memo =
  fun projectee  -> match projectee with | { n = n1; pos; vars;_} -> vars 
let (__proj__Mkbv__item__ppname : bv -> FStar_Ident.ident) =
  fun projectee  ->
    match projectee with | { ppname; index = index1; sort;_} -> ppname
  
let (__proj__Mkbv__item__index : bv -> Prims.int) =
  fun projectee  ->
    match projectee with | { ppname; index = index1; sort;_} -> index1
  
let (__proj__Mkbv__item__sort : bv -> term' syntax) =
  fun projectee  ->
    match projectee with | { ppname; index = index1; sort;_} -> sort
  
let (__proj__Mkfv__item__fv_name : fv -> var) =
  fun projectee  ->
    match projectee with | { fv_name; fv_delta; fv_qual;_} -> fv_name
  
let (__proj__Mkfv__item__fv_delta : fv -> delta_depth) =
  fun projectee  ->
    match projectee with | { fv_name; fv_delta; fv_qual;_} -> fv_delta
  
let (__proj__Mkfv__item__fv_qual :
  fv -> fv_qual FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { fv_name; fv_delta; fv_qual;_} -> fv_qual
  
let (__proj__Mkfree_vars__item__free_names : free_vars -> bv Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_names
  
let (__proj__Mkfree_vars__item__free_uvars :
  free_vars -> ctx_uvar Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_uvars
  
let (__proj__Mkfree_vars__item__free_univs :
  free_vars -> universe_uvar Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} -> free_univs
  
let (__proj__Mkfree_vars__item__free_univ_names :
  free_vars -> univ_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names; free_uvars; free_univs; free_univ_names;_} ->
        free_univ_names
  
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_effect
  
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> term' syntax FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_typ
  
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
  
let (__proj__Mklazyinfo__item__blob : lazyinfo -> FStar_Dyn.dyn) =
  fun projectee  ->
    match projectee with | { blob; lkind; ltyp; rng;_} -> blob
  
let (__proj__Mklazyinfo__item__lkind : lazyinfo -> lazy_kind) =
  fun projectee  ->
    match projectee with | { blob; lkind; ltyp; rng;_} -> lkind
  
let (__proj__Mklazyinfo__item__ltyp : lazyinfo -> term' syntax) =
  fun projectee  ->
    match projectee with | { blob; lkind; ltyp; rng;_} -> ltyp
  
let (__proj__Mklazyinfo__item__rng : lazyinfo -> FStar_Range.range) =
  fun projectee  -> match projectee with | { blob; lkind; ltyp; rng;_} -> rng 
let (uu___is_BadLazy : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | BadLazy  -> true | uu____4940 -> false
  
let (uu___is_Lazy_bv : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_bv  -> true | uu____4951 -> false
  
let (uu___is_Lazy_binder : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_binder  -> true | uu____4962 -> false
  
let (uu___is_Lazy_optionstate : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_optionstate  -> true | uu____4973 -> false
  
let (uu___is_Lazy_fvar : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_fvar  -> true | uu____4984 -> false
  
let (uu___is_Lazy_comp : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_comp  -> true | uu____4995 -> false
  
let (uu___is_Lazy_env : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_env  -> true | uu____5006 -> false
  
let (uu___is_Lazy_proofstate : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_proofstate  -> true | uu____5017 -> false
  
let (uu___is_Lazy_goal : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_goal  -> true | uu____5028 -> false
  
let (uu___is_Lazy_sigelt : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_sigelt  -> true | uu____5039 -> false
  
let (uu___is_Lazy_uvar : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_uvar  -> true | uu____5050 -> false
  
let (uu___is_Lazy_embedding : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_embedding _0 -> true | uu____5070 -> false
  
let (__proj__Lazy_embedding__item___0 :
  lazy_kind -> (emb_typ * term' syntax FStar_Common.thunk)) =
  fun projectee  -> match projectee with | Lazy_embedding _0 -> _0 
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____5113 -> false
  
let (__proj__Binding_var__item___0 : binding -> bv) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____5144 -> false
  
let (__proj__Binding_lid__item___0 :
  binding -> (FStar_Ident.lident * (univ_name Prims.list * term' syntax))) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____5199 -> false
  
let (__proj__Binding_univ__item___0 : binding -> univ_name) =
  fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit _0 -> true | uu____5219 -> false
  
let (__proj__Implicit__item___0 : arg_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Implicit _0 -> _0 
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____5243 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term' syntax) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____5267 -> false
  
type subst_ts = (subst_elt Prims.list Prims.list * maybe_set_use_range)
type ctx_uvar_and_subst =
  (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range))
type term = term' syntax
type uvar =
  (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
    version)
type uvars = ctx_uvar FStar_Util.set
type pat = pat' withinfo_t
type branch =
  (pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term'
    syntax)
type comp = comp' syntax
type ascription =
  ((term' syntax,comp' syntax) FStar_Util.either * term' syntax
    FStar_Pervasives_Native.option)
type antiquotations = (bv * term' syntax) Prims.list
type typ = term' syntax
type aqual = arg_qualifier FStar_Pervasives_Native.option
type arg = (term' syntax * arg_qualifier FStar_Pervasives_Native.option)
type args =
  (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list
type binder = (bv * arg_qualifier FStar_Pervasives_Native.option)
type binders = (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list
type lbname = (bv,fv) FStar_Util.either
type letbindings = (Prims.bool * letbinding Prims.list)
type freenames = bv FStar_Util.set
type attribute = term' syntax
type tscheme = (univ_name Prims.list * term' syntax)
type gamma = binding Prims.list
let (lazy_chooser :
  (lazy_kind -> lazyinfo -> term) FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
<<<<<<< HEAD
=======
let (mk_lcomp :
  FStar_Ident.lident -> typ -> cflag Prims.list -> (unit -> comp) -> lcomp) =
  fun eff_name  ->
    fun res_typ  ->
      fun cflags  ->
        fun comp_thunk  ->
          let uu____5627 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____5627 }
  
let (lcomp_comp : lcomp -> comp) =
  fun lc  ->
    let uu____5653 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____5653 with
    | FStar_Util.Inl thunk ->
        let c = thunk ()  in
        (FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr c); c)
    | FStar_Util.Inr c -> c
  
>>>>>>> snap
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
  | Abstract 
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
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Assumption  -> true | uu____5492 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____5503 -> false 
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____5514 -> false
=======
=======
>>>>>>> snap
    match projectee with | Assumption  -> true | uu____5806 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____5817 -> false 
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____5828 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____5525 -> false
  
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____5536 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____5547 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____5558 -> false
=======
    | uu____5839 -> false
  
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____5850 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____5861 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____5872 -> false
>>>>>>> snap
=======
    | uu____5839 -> false
  
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____5850 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____5861 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____5872 -> false
>>>>>>> snap
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____5569 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____5580 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____5591 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____5602 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____5613 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____5624 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____5635 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____5647 -> false
=======
    | uu____5883 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____5894 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____5905 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____5916 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____5927 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____5938 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____5949 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____5961 -> false
>>>>>>> snap
=======
    | uu____5883 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____5894 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____5905 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____5916 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____5927 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____5938 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____5949 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____5961 -> false
>>>>>>> snap
  
let (__proj__Reflectable__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Reflectable _0 -> _0 
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Discriminator _0 -> true | uu____5666 -> false
=======
    match projectee with | Discriminator _0 -> true | uu____5980 -> false
>>>>>>> snap
=======
    match projectee with | Discriminator _0 -> true | uu____5980 -> false
>>>>>>> snap
  
let (__proj__Discriminator__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Discriminator _0 -> _0 
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Projector _0 -> true | uu____5689 -> false
=======
    match projectee with | Projector _0 -> true | uu____6003 -> false
>>>>>>> snap
=======
    match projectee with | Projector _0 -> true | uu____6003 -> false
>>>>>>> snap
  
let (__proj__Projector__item___0 :
  qualifier -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | RecordType _0 -> true | uu____5728 -> false
=======
    match projectee with | RecordType _0 -> true | uu____6042 -> false
>>>>>>> snap
=======
    match projectee with | RecordType _0 -> true | uu____6042 -> false
>>>>>>> snap
  
let (__proj__RecordType__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee  -> match projectee with | RecordType _0 -> _0 
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | RecordConstructor _0 -> true | uu____5779 -> false
=======
    match projectee with | RecordConstructor _0 -> true | uu____6093 -> false
>>>>>>> snap
=======
    match projectee with | RecordConstructor _0 -> true | uu____6093 -> false
>>>>>>> snap
  
let (__proj__RecordConstructor__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee  -> match projectee with | RecordConstructor _0 -> _0 
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Action _0 -> true | uu____5822 -> false
=======
    match projectee with | Action _0 -> true | uu____6136 -> false
>>>>>>> snap
=======
    match projectee with | Action _0 -> true | uu____6136 -> false
>>>>>>> snap
  
let (__proj__Action__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Action _0 -> _0 
let (uu___is_ExceptionConstructor : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ExceptionConstructor  -> true
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____5840 -> false
  
let (uu___is_HasMaskedEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | HasMaskedEffect  -> true | uu____5851 -> false
  
let (uu___is_Effect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect  -> true | uu____5862 -> false
  
let (uu___is_OnlyName : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | OnlyName  -> true | uu____5873 -> false
=======
=======
>>>>>>> snap
    | uu____6154 -> false
  
let (uu___is_HasMaskedEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | HasMaskedEffect  -> true | uu____6165 -> false
  
let (uu___is_Effect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect  -> true | uu____6176 -> false
  
let (uu___is_OnlyName : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | OnlyName  -> true | uu____6187 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
type tycon = (FStar_Ident.lident * binders * typ)
type monad_abbrev = {
  mabbrev: FStar_Ident.lident ;
  parms: binders ;
  def: typ }
let (__proj__Mkmonad_abbrev__item__mabbrev :
  monad_abbrev -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { mabbrev; parms; def;_} -> mabbrev
  
let (__proj__Mkmonad_abbrev__item__parms : monad_abbrev -> binders) =
  fun projectee  -> match projectee with | { mabbrev; parms; def;_} -> parms 
let (__proj__Mkmonad_abbrev__item__def : monad_abbrev -> typ) =
  fun projectee  -> match projectee with | { mabbrev; parms; def;_} -> def 
type sub_eff =
  {
  source: FStar_Ident.lident ;
  target: FStar_Ident.lident ;
  lift_wp: tscheme FStar_Pervasives_Native.option ;
  lift: tscheme FStar_Pervasives_Native.option }
let (__proj__Mksub_eff__item__source : sub_eff -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { source; target; lift_wp; lift;_} -> source
  
let (__proj__Mksub_eff__item__target : sub_eff -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { source; target; lift_wp; lift;_} -> target
  
let (__proj__Mksub_eff__item__lift_wp :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { source; target; lift_wp; lift;_} -> lift_wp
  
let (__proj__Mksub_eff__item__lift :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_name
  
let (__proj__Mkaction__item__action_unqualified_name :
  action -> FStar_Ident.ident) =
  fun projectee  ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_unqualified_name
  
let (__proj__Mkaction__item__action_univs : action -> univ_names) =
  fun projectee  ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_univs
  
let (__proj__Mkaction__item__action_params : action -> binders) =
  fun projectee  ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_params
  
let (__proj__Mkaction__item__action_defn : action -> term) =
  fun projectee  ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_defn
  
let (__proj__Mkaction__item__action_typ : action -> typ) =
  fun projectee  ->
    match projectee with
    | { action_name; action_unqualified_name; action_univs; action_params;
        action_defn; action_typ;_} -> action_typ
  
type match_with_close =
  {
  if_then_else: tscheme ;
  ite_wp: tscheme ;
  close_wp: tscheme }
let (__proj__Mkmatch_with_close__item__if_then_else :
  match_with_close -> tscheme) =
  fun projectee  ->
    match projectee with
    | { if_then_else; ite_wp; close_wp;_} -> if_then_else
  
let (__proj__Mkmatch_with_close__item__ite_wp : match_with_close -> tscheme)
  =
  fun projectee  ->
    match projectee with | { if_then_else; ite_wp; close_wp;_} -> ite_wp
  
let (__proj__Mkmatch_with_close__item__close_wp :
  match_with_close -> tscheme) =
  fun projectee  ->
    match projectee with | { if_then_else; ite_wp; close_wp;_} -> close_wp
  
type match_with_subst = {
  conjunction: tscheme }
let (__proj__Mkmatch_with_subst__item__conjunction :
  match_with_subst -> tscheme) =
  fun projectee  -> match projectee with | { conjunction;_} -> conjunction 
type eff_decl =
  {
  is_layered:
    (Prims.bool * FStar_Ident.lident FStar_Pervasives_Native.option) ;
  cattributes: cflag Prims.list ;
  mname: FStar_Ident.lident ;
  univs: univ_names ;
  binders: binders ;
  signature: tscheme ;
  ret_wp: tscheme ;
  bind_wp: tscheme ;
  stronger: tscheme ;
  match_wps: (match_with_close,match_with_subst) FStar_Util.either ;
  trivial: tscheme FStar_Pervasives_Native.option ;
  repr: tscheme ;
  return_repr: tscheme ;
  bind_repr: tscheme ;
  stronger_repr: tscheme FStar_Pervasives_Native.option ;
  actions: action Prims.list ;
  eff_attrs: attribute Prims.list }
let (__proj__Mkeff_decl__item__is_layered :
  eff_decl ->
    (Prims.bool * FStar_Ident.lident FStar_Pervasives_Native.option))
  =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> is_layered
  
let (__proj__Mkeff_decl__item__cattributes : eff_decl -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> cattributes
  
let (__proj__Mkeff_decl__item__mname : eff_decl -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> mname
  
let (__proj__Mkeff_decl__item__univs : eff_decl -> univ_names) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> univs
  
let (__proj__Mkeff_decl__item__binders : eff_decl -> binders) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> binders
  
let (__proj__Mkeff_decl__item__signature : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> signature
  
let (__proj__Mkeff_decl__item__ret_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> ret_wp
  
let (__proj__Mkeff_decl__item__bind_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> bind_wp
  
let (__proj__Mkeff_decl__item__stronger : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> stronger
  
let (__proj__Mkeff_decl__item__match_wps :
  eff_decl -> (match_with_close,match_with_subst) FStar_Util.either) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> match_wps
  
let (__proj__Mkeff_decl__item__trivial :
  eff_decl -> tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> trivial
  
let (__proj__Mkeff_decl__item__repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> repr
  
let (__proj__Mkeff_decl__item__return_repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> return_repr
  
let (__proj__Mkeff_decl__item__bind_repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> bind_repr
  
let (__proj__Mkeff_decl__item__stronger_repr :
  eff_decl -> tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> stronger_repr
  
let (__proj__Mkeff_decl__item__actions : eff_decl -> action Prims.list) =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> actions
  
let (__proj__Mkeff_decl__item__eff_attrs : eff_decl -> attribute Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { is_layered; cattributes; mname; univs; binders; signature; ret_wp;
        bind_wp; stronger; match_wps; trivial; repr; return_repr; bind_repr;
        stronger_repr; actions; eff_attrs;_} -> eff_attrs
  
type sig_metadata =
  {
  sigmeta_active: Prims.bool ;
  sigmeta_fact_db_ids: Prims.string Prims.list }
let (__proj__Mksig_metadata__item__sigmeta_active :
  sig_metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids;_} -> sigmeta_active
  
let (__proj__Mksig_metadata__item__sigmeta_fact_db_ids :
  sig_metadata -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigmeta_active; sigmeta_fact_db_ids;_} -> sigmeta_fact_db_ids
  
type sigelt' =
  | Sig_inductive_typ of (FStar_Ident.lident * univ_names * binders * typ *
  FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list) 
  | Sig_bundle of (sigelt Prims.list * FStar_Ident.lident Prims.list) 
  | Sig_datacon of (FStar_Ident.lident * univ_names * typ *
  FStar_Ident.lident * Prims.int * FStar_Ident.lident Prims.list) 
  | Sig_declare_typ of (FStar_Ident.lident * univ_names * typ) 
  | Sig_let of (letbindings * FStar_Ident.lident Prims.list) 
  | Sig_main of term 
  | Sig_assume of (FStar_Ident.lident * univ_names * formula) 
  | Sig_new_effect of eff_decl 
  | Sig_new_effect_for_free of eff_decl 
  | Sig_sub_effect of sub_eff 
  | Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp *
  cflag Prims.list) 
  | Sig_pragma of pragma 
  | Sig_splice of (FStar_Ident.lident Prims.list * term) 
and sigelt =
  {
  sigel: sigelt' ;
  sigrng: FStar_Range.range ;
  sigquals: qualifier Prims.list ;
  sigmeta: sig_metadata ;
  sigattrs: attribute Prims.list ;
  sigopts: FStar_Options.optionstate FStar_Pervasives_Native.option }
let (uu___is_Sig_inductive_typ : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_inductive_typ _0 -> true | uu____7184 -> false
=======
    match projectee with | Sig_inductive_typ _0 -> true | uu____7271 -> false
>>>>>>> snap
=======
    match projectee with | Sig_inductive_typ _0 -> true | uu____7271 -> false
>>>>>>> snap
=======
    match projectee with | Sig_inductive_typ _0 -> true | uu____7323 -> false
>>>>>>> snap
  
let (__proj__Sig_inductive_typ__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident
      Prims.list * FStar_Ident.lident Prims.list))
  = fun projectee  -> match projectee with | Sig_inductive_typ _0 -> _0 
let (uu___is_Sig_bundle : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_bundle _0 -> true | uu____7259 -> false
=======
    match projectee with | Sig_bundle _0 -> true | uu____7346 -> false
>>>>>>> snap
=======
    match projectee with | Sig_bundle _0 -> true | uu____7346 -> false
>>>>>>> snap
=======
    match projectee with | Sig_bundle _0 -> true | uu____7398 -> false
>>>>>>> snap
  
let (__proj__Sig_bundle__item___0 :
  sigelt' -> (sigelt Prims.list * FStar_Ident.lident Prims.list)) =
  fun projectee  -> match projectee with | Sig_bundle _0 -> _0 
let (uu___is_Sig_datacon : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_datacon _0 -> true | uu____7317 -> false
=======
    match projectee with | Sig_datacon _0 -> true | uu____7404 -> false
>>>>>>> snap
=======
    match projectee with | Sig_datacon _0 -> true | uu____7404 -> false
>>>>>>> snap
=======
    match projectee with | Sig_datacon _0 -> true | uu____7456 -> false
>>>>>>> snap
  
let (__proj__Sig_datacon__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int *
      FStar_Ident.lident Prims.list))
  = fun projectee  -> match projectee with | Sig_datacon _0 -> _0 
let (uu___is_Sig_declare_typ : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_declare_typ _0 -> true | uu____7387 -> false
=======
    match projectee with | Sig_declare_typ _0 -> true | uu____7474 -> false
>>>>>>> snap
=======
    match projectee with | Sig_declare_typ _0 -> true | uu____7474 -> false
>>>>>>> snap
=======
    match projectee with | Sig_declare_typ _0 -> true | uu____7526 -> false
>>>>>>> snap
  
let (__proj__Sig_declare_typ__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * typ)) =
  fun projectee  -> match projectee with | Sig_declare_typ _0 -> _0 
let (uu___is_Sig_let : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_let _0 -> true | uu____7430 -> false
=======
    match projectee with | Sig_let _0 -> true | uu____7517 -> false
>>>>>>> snap
=======
    match projectee with | Sig_let _0 -> true | uu____7517 -> false
>>>>>>> snap
=======
    match projectee with | Sig_let _0 -> true | uu____7569 -> false
>>>>>>> snap
  
let (__proj__Sig_let__item___0 :
  sigelt' -> (letbindings * FStar_Ident.lident Prims.list)) =
  fun projectee  -> match projectee with | Sig_let _0 -> _0 
let (uu___is_Sig_main : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_main _0 -> true | uu____7467 -> false
=======
    match projectee with | Sig_main _0 -> true | uu____7554 -> false
>>>>>>> snap
=======
    match projectee with | Sig_main _0 -> true | uu____7554 -> false
>>>>>>> snap
=======
    match projectee with | Sig_main _0 -> true | uu____7606 -> false
>>>>>>> snap
  
let (__proj__Sig_main__item___0 : sigelt' -> term) =
  fun projectee  -> match projectee with | Sig_main _0 -> _0 
let (uu___is_Sig_assume : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_assume _0 -> true | uu____7492 -> false
=======
    match projectee with | Sig_assume _0 -> true | uu____7579 -> false
>>>>>>> snap
=======
    match projectee with | Sig_assume _0 -> true | uu____7579 -> false
>>>>>>> snap
=======
    match projectee with | Sig_assume _0 -> true | uu____7631 -> false
>>>>>>> snap
  
let (__proj__Sig_assume__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * formula)) =
  fun projectee  -> match projectee with | Sig_assume _0 -> _0 
let (uu___is_Sig_new_effect : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_new_effect _0 -> true | uu____7529 -> false
=======
    match projectee with | Sig_new_effect _0 -> true | uu____7616 -> false
>>>>>>> snap
=======
    match projectee with | Sig_new_effect _0 -> true | uu____7616 -> false
>>>>>>> snap
=======
    match projectee with | Sig_new_effect _0 -> true | uu____7668 -> false
>>>>>>> snap
  
let (__proj__Sig_new_effect__item___0 : sigelt' -> eff_decl) =
  fun projectee  -> match projectee with | Sig_new_effect _0 -> _0 
let (uu___is_Sig_new_effect_for_free : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Sig_new_effect_for_free _0 -> true
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____7548 -> false
=======
    | uu____7635 -> false
>>>>>>> snap
=======
    | uu____7635 -> false
>>>>>>> snap
=======
    | uu____7687 -> false
>>>>>>> snap
  
let (__proj__Sig_new_effect_for_free__item___0 : sigelt' -> eff_decl) =
  fun projectee  -> match projectee with | Sig_new_effect_for_free _0 -> _0 
let (uu___is_Sig_sub_effect : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_sub_effect _0 -> true | uu____7567 -> false
=======
    match projectee with | Sig_sub_effect _0 -> true | uu____7654 -> false
>>>>>>> snap
=======
    match projectee with | Sig_sub_effect _0 -> true | uu____7654 -> false
>>>>>>> snap
=======
    match projectee with | Sig_sub_effect _0 -> true | uu____7706 -> false
>>>>>>> snap
  
let (__proj__Sig_sub_effect__item___0 : sigelt' -> sub_eff) =
  fun projectee  -> match projectee with | Sig_sub_effect _0 -> _0 
let (uu___is_Sig_effect_abbrev : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_effect_abbrev _0 -> true | uu____7598 -> false
=======
    match projectee with | Sig_effect_abbrev _0 -> true | uu____7685 -> false
>>>>>>> snap
=======
    match projectee with | Sig_effect_abbrev _0 -> true | uu____7685 -> false
>>>>>>> snap
=======
    match projectee with | Sig_effect_abbrev _0 -> true | uu____7737 -> false
>>>>>>> snap
  
let (__proj__Sig_effect_abbrev__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * comp * cflag Prims.list))
  = fun projectee  -> match projectee with | Sig_effect_abbrev _0 -> _0 
let (uu___is_Sig_pragma : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_pragma _0 -> true | uu____7653 -> false
=======
    match projectee with | Sig_pragma _0 -> true | uu____7740 -> false
>>>>>>> snap
=======
    match projectee with | Sig_pragma _0 -> true | uu____7740 -> false
>>>>>>> snap
=======
    match projectee with | Sig_pragma _0 -> true | uu____7792 -> false
>>>>>>> snap
  
let (__proj__Sig_pragma__item___0 : sigelt' -> pragma) =
  fun projectee  -> match projectee with | Sig_pragma _0 -> _0 
let (uu___is_Sig_splice : sigelt' -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Sig_splice _0 -> true | uu____7678 -> false
=======
    match projectee with | Sig_splice _0 -> true | uu____7765 -> false
>>>>>>> snap
=======
    match projectee with | Sig_splice _0 -> true | uu____7765 -> false
>>>>>>> snap
=======
    match projectee with | Sig_splice _0 -> true | uu____7817 -> false
>>>>>>> snap
  
let (__proj__Sig_splice__item___0 :
  sigelt' -> (FStar_Ident.lident Prims.list * term)) =
  fun projectee  -> match projectee with | Sig_splice _0 -> _0 
let (__proj__Mksigelt__item__sigel : sigelt -> sigelt') =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigel
  
let (__proj__Mksigelt__item__sigrng : sigelt -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigrng
  
let (__proj__Mksigelt__item__sigquals : sigelt -> qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigquals
  
let (__proj__Mksigelt__item__sigmeta : sigelt -> sig_metadata) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigmeta
  
let (__proj__Mksigelt__item__sigattrs : sigelt -> attribute Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigattrs
  
let (__proj__Mksigelt__item__sigopts :
  sigelt -> FStar_Options.optionstate FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts;_} -> sigopts
  
type sigelts = sigelt Prims.list
type modul =
  {
  name: FStar_Ident.lident ;
  declarations: sigelts ;
  exports: sigelts ;
  is_interface: Prims.bool }
let (__proj__Mkmodul__item__name : modul -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { name; declarations; exports; is_interface;_} -> name
  
let (__proj__Mkmodul__item__declarations : modul -> sigelts) =
  fun projectee  ->
    match projectee with
    | { name; declarations; exports; is_interface;_} -> declarations
  
let (__proj__Mkmodul__item__exports : modul -> sigelts) =
  fun projectee  ->
    match projectee with
    | { name; declarations; exports; is_interface;_} -> exports
  
let (__proj__Mkmodul__item__is_interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name; declarations; exports; is_interface;_} -> is_interface
  
let (mod_name : modul -> FStar_Ident.lident) = fun m  -> m.name 
type path = Prims.string Prims.list
type subst_t = subst_elt Prims.list
type 'a mk_t_a =
  unit FStar_Pervasives_Native.option -> FStar_Range.range -> 'a syntax
type mk_t = term' mk_t_a
let (contains_reflectable : qualifier Prims.list -> Prims.bool) =
  fun l  ->
    FStar_Util.for_some
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      (fun uu___0_7900  ->
         match uu___0_7900 with
         | Reflectable uu____7902 -> true
         | uu____7904 -> false) l
=======
=======
>>>>>>> snap
      (fun uu___0_8024  ->
         match uu___0_8024 with
         | Reflectable uu____8026 -> true
         | uu____8028 -> false) l
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      (fun uu___0_8076  ->
         match uu___0_8076 with
         | Reflectable uu____8078 -> true
         | uu____8080 -> false) l
>>>>>>> snap
  
let withinfo : 'a . 'a -> FStar_Range.range -> 'a withinfo_t =
  fun v1  -> fun r  -> { v = v1; p = r } 
let withsort : 'a . 'a -> 'a withinfo_t =
  fun v1  -> withinfo v1 FStar_Range.dummyRange 
let (bv_eq : bv -> bv -> Prims.bool) =
  fun bv1  ->
    fun bv2  ->
      ((bv1.ppname).FStar_Ident.idText = (bv2.ppname).FStar_Ident.idText) &&
        (bv1.index = bv2.index)
  
let (order_bv : bv -> bv -> Prims.int) =
  fun x  ->
    fun y  ->
      let i =
        FStar_String.compare (x.ppname).FStar_Ident.idText
          (y.ppname).FStar_Ident.idText
         in
      if i = Prims.int_zero then x.index - y.index else i
  
let (order_ident : FStar_Ident.ident -> FStar_Ident.ident -> Prims.int) =
  fun x  ->
    fun y  -> FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText
  
let (order_fv : FStar_Ident.lident -> FStar_Ident.lident -> Prims.int) =
  fun x  ->
    fun y  -> FStar_String.compare x.FStar_Ident.str y.FStar_Ident.str
  
let (range_of_lbname : lbname -> FStar_Range.range) =
  fun l  ->
    match l with
    | FStar_Util.Inl x -> (x.ppname).FStar_Ident.idRange
    | FStar_Util.Inr fv -> FStar_Ident.range_of_lid (fv.fv_name).v
  
let (range_of_bv : bv -> FStar_Range.range) =
  fun x  -> (x.ppname).FStar_Ident.idRange 
let (set_range_of_bv : bv -> FStar_Range.range -> bv) =
  fun x  ->
    fun r  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu___398_8022 = x  in
      let uu____8023 =
        FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____8023;
        index = (uu___398_8022.index);
        sort = (uu___398_8022.sort)
=======
      let uu___416_8146 = x  in
      let uu____8147 =
        FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____8147;
        index = (uu___416_8146.index);
        sort = (uu___416_8146.sort)
>>>>>>> snap
=======
      let uu___416_8146 = x  in
      let uu____8147 =
        FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____8147;
        index = (uu___416_8146.index);
        sort = (uu___416_8146.sort)
>>>>>>> snap
=======
      let uu___401_8198 = x  in
      let uu____8199 =
        FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____8199;
        index = (uu___401_8198.index);
        sort = (uu___401_8198.sort)
>>>>>>> snap
      }
  
let (on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo) =
  fun f  ->
    fun qi  ->
      let aq =
        FStar_List.map
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          (fun uu____8060  ->
             match uu____8060 with
             | (bv,t) -> let uu____8071 = f t  in (bv, uu____8071))
          qi.antiquotes
         in
      let uu___406_8072 = qi  in
      { qkind = (uu___406_8072.qkind); antiquotes = aq }
=======
          (fun uu____8184  ->
             match uu____8184 with
             | (bv,t) -> let uu____8195 = f t  in (bv, uu____8195))
          qi.antiquotes
         in
      let uu___424_8196 = qi  in
      { qkind = (uu___424_8196.qkind); antiquotes = aq }
>>>>>>> snap
=======
          (fun uu____8184  ->
             match uu____8184 with
             | (bv,t) -> let uu____8195 = f t  in (bv, uu____8195))
          qi.antiquotes
         in
      let uu___424_8196 = qi  in
      { qkind = (uu___424_8196.qkind); antiquotes = aq }
>>>>>>> snap
=======
          (fun uu____8236  ->
             match uu____8236 with
             | (bv,t) -> let uu____8247 = f t  in (bv, uu____8247))
          qi.antiquotes
         in
      let uu___409_8248 = qi  in
      { qkind = (uu___409_8248.qkind); antiquotes = aq }
>>>>>>> snap
  
let (lookup_aq : bv -> antiquotations -> term FStar_Pervasives_Native.option)
  =
  fun bv  ->
    fun aq  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____8088 =
        FStar_List.tryFind
          (fun uu____8106  ->
             match uu____8106 with | (bv',uu____8115) -> bv_eq bv bv') aq
         in
      match uu____8088 with
      | FStar_Pervasives_Native.Some (uu____8122,e) ->
=======
=======
>>>>>>> snap
      let uu____8212 =
        FStar_List.tryFind
          (fun uu____8230  ->
             match uu____8230 with | (bv',uu____8239) -> bv_eq bv bv') aq
         in
      match uu____8212 with
      | FStar_Pervasives_Native.Some (uu____8246,e) ->
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      let uu____8264 =
        FStar_List.tryFind
          (fun uu____8282  ->
             match uu____8282 with | (bv',uu____8291) -> bv_eq bv bv') aq
         in
      match uu____8264 with
      | FStar_Pervasives_Native.Some (uu____8298,e) ->
>>>>>>> snap
          FStar_Pervasives_Native.Some e
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let syn :
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
  'Auu____8153 'Auu____8154 'Auu____8155 .
    'Auu____8153 ->
      'Auu____8154 ->
        ('Auu____8154 -> 'Auu____8153 -> 'Auu____8155) -> 'Auu____8155
  = fun p  -> fun k  -> fun f  -> f k p 
let mk_fvs :
  'Auu____8186 .
    unit -> 'Auu____8186 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8195  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let mk_uvs :
  'Auu____8203 .
    unit -> 'Auu____8203 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8212  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (new_bv_set : unit -> bv FStar_Util.set) =
  fun uu____8222  -> FStar_Util.new_set order_bv 
let (new_id_set : unit -> FStar_Ident.ident FStar_Util.set) =
  fun uu____8232  -> FStar_Util.new_set order_ident 
let (new_fv_set : unit -> FStar_Ident.lident FStar_Util.set) =
  fun uu____8242  -> FStar_Util.new_set order_fv 
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x  ->
    fun y  ->
      let uu____8257 = FStar_Ident.text_of_id x  in
      let uu____8259 = FStar_Ident.text_of_id y  in
      FStar_String.compare uu____8257 uu____8259
  
let (new_universe_names_set : unit -> univ_name FStar_Util.set) =
  fun uu____8268  -> FStar_Util.new_set order_univ_name 
=======
=======
>>>>>>> snap
  'Auu____8277 'Auu____8278 'Auu____8279 .
    'Auu____8277 ->
      'Auu____8278 ->
        ('Auu____8278 -> 'Auu____8277 -> 'Auu____8279) -> 'Auu____8279
  = fun p  -> fun k  -> fun f  -> f k p 
let mk_fvs :
  'Auu____8310 .
    unit -> 'Auu____8310 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8319  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let mk_uvs :
  'Auu____8327 .
    unit -> 'Auu____8327 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8336  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (new_bv_set : unit -> bv FStar_Util.set) =
  fun uu____8346  -> FStar_Util.new_set order_bv 
let (new_id_set : unit -> FStar_Ident.ident FStar_Util.set) =
  fun uu____8356  -> FStar_Util.new_set order_ident 
let (new_fv_set : unit -> FStar_Ident.lident FStar_Util.set) =
  fun uu____8366  -> FStar_Util.new_set order_fv 
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x  ->
    fun y  ->
      let uu____8381 = FStar_Ident.text_of_id x  in
      let uu____8383 = FStar_Ident.text_of_id y  in
      FStar_String.compare uu____8381 uu____8383
  
let (new_universe_names_set : unit -> univ_name FStar_Util.set) =
  fun uu____8392  -> FStar_Util.new_set order_univ_name 
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
  'Auu____8329 'Auu____8330 'Auu____8331 .
    'Auu____8329 ->
      'Auu____8330 ->
        ('Auu____8330 -> 'Auu____8329 -> 'Auu____8331) -> 'Auu____8331
  = fun p  -> fun k  -> fun f  -> f k p 
let mk_fvs :
  'Auu____8362 .
    unit -> 'Auu____8362 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8371  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let mk_uvs :
  'Auu____8379 .
    unit -> 'Auu____8379 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8388  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (new_bv_set : unit -> bv FStar_Util.set) =
  fun uu____8398  -> FStar_Util.new_set order_bv 
let (new_id_set : unit -> FStar_Ident.ident FStar_Util.set) =
  fun uu____8408  -> FStar_Util.new_set order_ident 
let (new_fv_set : unit -> FStar_Ident.lident FStar_Util.set) =
  fun uu____8418  -> FStar_Util.new_set order_fv 
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x  ->
    fun y  ->
      let uu____8433 = FStar_Ident.text_of_id x  in
      let uu____8435 = FStar_Ident.text_of_id y  in
      FStar_String.compare uu____8433 uu____8435
  
let (new_universe_names_set : unit -> univ_name FStar_Util.set) =
  fun uu____8444  -> FStar_Util.new_set order_univ_name 
>>>>>>> snap
let (eq_binding : binding -> binding -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with
      | (Binding_var bv1,Binding_var bv2) -> bv_eq bv1 bv2
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      | (Binding_lid (lid1,uu____8287),Binding_lid (lid2,uu____8289)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1,Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu____8324 -> false
=======
      | (Binding_lid (lid1,uu____8411),Binding_lid (lid2,uu____8413)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1,Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu____8448 -> false
>>>>>>> snap
=======
      | (Binding_lid (lid1,uu____8411),Binding_lid (lid2,uu____8413)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1,Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu____8448 -> false
>>>>>>> snap
=======
      | (Binding_lid (lid1,uu____8463),Binding_lid (lid2,uu____8465)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1,Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu____8500 -> false
>>>>>>> snap
  
let (no_names : freenames) = new_bv_set () 
let (no_fvars : FStar_Ident.lident FStar_Util.set) = new_fv_set () 
let (no_universe_names : univ_name FStar_Util.set) =
  new_universe_names_set () 
let (freenames_of_list : bv Prims.list -> freenames) =
  fun l  -> FStar_List.fold_right FStar_Util.set_add l no_names 
let (list_of_freenames : freenames -> bv Prims.list) =
  fun fvs  -> FStar_Util.set_elements fvs 
let mk : 'a . 'a -> 'a mk_t_a =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    fun uu____8378  ->
      fun r  ->
        let uu____8382 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        { n = t; pos = r; vars = uu____8382 }
  
let (bv_to_tm : bv -> term) =
  fun bv  ->
    let uu____8393 = range_of_bv bv  in
    mk (Tm_bvar bv) FStar_Pervasives_Native.None uu____8393
  
let (bv_to_name : bv -> term) =
  fun bv  ->
    let uu____8400 = range_of_bv bv  in
    mk (Tm_name bv) FStar_Pervasives_Native.None uu____8400
=======
=======
>>>>>>> snap
    fun uu____8502  ->
      fun r  ->
        let uu____8506 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        { n = t; pos = r; vars = uu____8506 }
  
let (bv_to_tm : bv -> term) =
  fun bv  ->
    let uu____8517 = range_of_bv bv  in
    mk (Tm_bvar bv) FStar_Pervasives_Native.None uu____8517
  
let (bv_to_name : bv -> term) =
  fun bv  ->
    let uu____8524 = range_of_bv bv  in
    mk (Tm_name bv) FStar_Pervasives_Native.None uu____8524
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
    fun uu____8554  ->
      fun r  ->
        let uu____8558 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        { n = t; pos = r; vars = uu____8558 }
  
let (bv_to_tm : bv -> term) =
  fun bv  ->
    let uu____8569 = range_of_bv bv  in
    mk (Tm_bvar bv) FStar_Pervasives_Native.None uu____8569
  
let (bv_to_name : bv -> term) =
  fun bv  ->
    let uu____8576 = range_of_bv bv  in
    mk (Tm_name bv) FStar_Pervasives_Native.None uu____8576
>>>>>>> snap
  
let (binders_to_names : binders -> term Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.map
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
         (fun uu____8430  ->
            match uu____8430 with | (x,uu____8438) -> bv_to_name x))
=======
         (fun uu____8554  ->
            match uu____8554 with | (x,uu____8562) -> bv_to_name x))
>>>>>>> snap
=======
         (fun uu____8554  ->
            match uu____8554 with | (x,uu____8562) -> bv_to_name x))
>>>>>>> snap
=======
         (fun uu____8606  ->
            match uu____8606 with | (x,uu____8614) -> bv_to_name x))
>>>>>>> snap
  
let (mk_Tm_app : term -> args -> mk_t) =
  fun t1  ->
    fun args  ->
      fun k  ->
        fun p  ->
          match args with
          | [] -> t1
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          | uu____8468 ->
=======
          | uu____8592 ->
>>>>>>> snap
=======
          | uu____8592 ->
>>>>>>> snap
=======
          | uu____8644 ->
>>>>>>> snap
              mk (Tm_app (t1, args)) FStar_Pervasives_Native.None p
  
let (mk_Tm_uinst : term -> universes -> term) =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    fun uu___1_8493  ->
      match uu___1_8493 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____8495 ->
               mk (Tm_uinst (t, us)) FStar_Pervasives_Native.None t.pos
           | uu____8498 -> failwith "Unexpected universe instantiation")
=======
=======
>>>>>>> snap
    fun uu___1_8617  ->
      match uu___1_8617 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____8619 ->
               mk (Tm_uinst (t, us)) FStar_Pervasives_Native.None t.pos
           | uu____8622 -> failwith "Unexpected universe instantiation")
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
    fun uu___1_8669  ->
      match uu___1_8669 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____8671 ->
               mk (Tm_uinst (t, us)) FStar_Pervasives_Native.None t.pos
           | uu____8674 -> failwith "Unexpected universe instantiation")
>>>>>>> snap
  
let (extend_app_n : term -> args -> mk_t) =
  fun t  ->
    fun args'  ->
      fun kopt  ->
        fun r  ->
          match t.n with
          | Tm_app (head1,args) ->
              mk_Tm_app head1 (FStar_List.append args args') kopt r
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          | uu____8557 -> mk_Tm_app t args' kopt r
=======
          | uu____8681 -> mk_Tm_app t args' kopt r
>>>>>>> snap
=======
          | uu____8681 -> mk_Tm_app t args' kopt r
>>>>>>> snap
=======
          | uu____8733 -> mk_Tm_app t args' kopt r
>>>>>>> snap
  
let (extend_app : term -> arg -> mk_t) =
  fun t  -> fun arg  -> fun kopt  -> fun r  -> extend_app_n t [arg] kopt r 
let (mk_Tm_delayed : (term * subst_ts) -> FStar_Range.range -> term) =
  fun lr  ->
    fun pos  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____8614 =
        let uu____8621 =
          let uu____8622 =
            let uu____8645 = FStar_Util.mk_ref FStar_Pervasives_Native.None
               in
            (lr, uu____8645)  in
          Tm_delayed uu____8622  in
        mk uu____8621  in
      uu____8614 FStar_Pervasives_Native.None pos
=======
      let uu____8738 =
        let uu____8745 =
          let uu____8746 =
            let uu____8769 = FStar_Util.mk_ref FStar_Pervasives_Native.None
               in
=======
      let uu____8738 =
        let uu____8745 =
          let uu____8746 =
            let uu____8769 = FStar_Util.mk_ref FStar_Pervasives_Native.None
               in
>>>>>>> snap
            (lr, uu____8769)  in
          Tm_delayed uu____8746  in
        mk uu____8745  in
      uu____8738 FStar_Pervasives_Native.None pos
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      let uu____8790 =
        let uu____8797 =
          let uu____8798 =
            let uu____8821 = FStar_Util.mk_ref FStar_Pervasives_Native.None
               in
            (lr, uu____8821)  in
          Tm_delayed uu____8798  in
        mk uu____8797  in
      uu____8790 FStar_Pervasives_Native.None pos
>>>>>>> snap
  
let (mk_Total' : typ -> universe FStar_Pervasives_Native.option -> comp) =
  fun t  -> fun u  -> mk (Total (t, u)) FStar_Pervasives_Native.None t.pos 
let (mk_GTotal' : typ -> universe FStar_Pervasives_Native.option -> comp) =
  fun t  -> fun u  -> mk (GTotal (t, u)) FStar_Pervasives_Native.None t.pos 
let (mk_Total : typ -> comp) =
  fun t  -> mk_Total' t FStar_Pervasives_Native.None 
let (mk_GTotal : typ -> comp) =
  fun t  -> mk_GTotal' t FStar_Pervasives_Native.None 
let (mk_Comp : comp_typ -> comp) =
  fun ct  -> mk (Comp ct) FStar_Pervasives_Native.None (ct.result_typ).pos 
let (mk_lb :
  (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term *
    attribute Prims.list * FStar_Range.range) -> letbinding)
  =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
  fun uu____8753  ->
    match uu____8753 with
=======
  fun uu____8877  ->
    match uu____8877 with
>>>>>>> snap
=======
  fun uu____8877  ->
    match uu____8877 with
>>>>>>> snap
=======
  fun uu____8929  ->
    match uu____8929 with
>>>>>>> snap
    | (x,univs,eff,t,e,attrs,pos) ->
        {
          lbname = x;
          lbunivs = univs;
          lbtyp = t;
          lbeff = eff;
          lbdef = e;
          lbattrs = attrs;
          lbpos = pos
        }
  
let (default_sigmeta : sig_metadata) =
  { sigmeta_active = true; sigmeta_fact_db_ids = [] } 
let (mk_sigelt : sigelt' -> sigelt) =
  fun e  ->
    {
      sigel = e;
      sigrng = FStar_Range.dummyRange;
      sigquals = [];
      sigmeta = default_sigmeta;
      sigattrs = [];
      sigopts = FStar_Pervasives_Native.None
    }
  
let (mk_subst : subst_t -> subst_t) = fun s  -> s 
let (extend_subst : subst_elt -> subst_elt Prims.list -> subst_t) =
  fun x  -> fun s  -> x :: s 
let (argpos : arg -> FStar_Range.range) =
  fun x  -> (FStar_Pervasives_Native.fst x).pos 
let (tun : term) =
  mk Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (teff : term) =
  mk (Tm_constant FStar_Const.Const_effect) FStar_Pervasives_Native.None
    FStar_Range.dummyRange
  
let (is_teff : term -> Prims.bool) =
  fun t  ->
    match t.n with
    | Tm_constant (FStar_Const.Const_effect ) -> true
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____8838 -> false
  
let (is_type : term -> Prims.bool) =
  fun t  -> match t.n with | Tm_type uu____8848 -> true | uu____8850 -> false 
=======
=======
>>>>>>> snap
    | uu____8962 -> false
  
let (is_type : term -> Prims.bool) =
  fun t  -> match t.n with | Tm_type uu____8972 -> true | uu____8974 -> false 
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
    | uu____9014 -> false
  
let (is_type : term -> Prims.bool) =
  fun t  -> match t.n with | Tm_type uu____9024 -> true | uu____9026 -> false 
>>>>>>> snap
let (null_id : FStar_Ident.ident) =
  FStar_Ident.mk_ident ("_", FStar_Range.dummyRange) 
let (null_bv : term -> bv) =
  fun k  -> { ppname = null_id; index = Prims.int_zero; sort = k } 
let (mk_binder : bv -> binder) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (null_binder : term -> binder) =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____8876 = null_bv t  in (uu____8876, FStar_Pervasives_Native.None)
=======
    let uu____9000 = null_bv t  in (uu____9000, FStar_Pervasives_Native.None)
>>>>>>> snap
=======
    let uu____9000 = null_bv t  in (uu____9000, FStar_Pervasives_Native.None)
>>>>>>> snap
=======
    let uu____9052 = null_bv t  in (uu____9052, FStar_Pervasives_Native.None)
>>>>>>> snap
  
let (imp_tag : arg_qualifier) = Implicit false 
let (iarg : term -> arg) =
  fun t  -> (t, (FStar_Pervasives_Native.Some imp_tag)) 
let (as_arg : term -> arg) = fun t  -> (t, FStar_Pervasives_Native.None) 
let (is_null_bv : bv -> Prims.bool) =
  fun b  -> (b.ppname).FStar_Ident.idText = null_id.FStar_Ident.idText 
let (is_null_binder : binder -> Prims.bool) =
  fun b  -> is_null_bv (FStar_Pervasives_Native.fst b) 
let (is_top_level : letbinding Prims.list -> Prims.bool) =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
  fun uu___2_8926  ->
    match uu___2_8926 with
    | { lbname = FStar_Util.Inr uu____8930; lbunivs = uu____8931;
        lbtyp = uu____8932; lbeff = uu____8933; lbdef = uu____8934;
        lbattrs = uu____8935; lbpos = uu____8936;_}::uu____8937 -> true
    | uu____8951 -> false
=======
=======
>>>>>>> snap
  fun uu___2_9050  ->
    match uu___2_9050 with
    | { lbname = FStar_Util.Inr uu____9054; lbunivs = uu____9055;
        lbtyp = uu____9056; lbeff = uu____9057; lbdef = uu____9058;
        lbattrs = uu____9059; lbpos = uu____9060;_}::uu____9061 -> true
    | uu____9075 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
  fun uu___2_9102  ->
    match uu___2_9102 with
    | { lbname = FStar_Util.Inr uu____9106; lbunivs = uu____9107;
        lbtyp = uu____9108; lbeff = uu____9109; lbdef = uu____9110;
        lbattrs = uu____9111; lbpos = uu____9112;_}::uu____9113 -> true
    | uu____9127 -> false
>>>>>>> snap
  
let (freenames_of_binders : binders -> freenames) =
  fun bs  ->
    FStar_List.fold_right
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      (fun uu____8973  ->
         fun out  ->
           match uu____8973 with | (x,uu____8986) -> FStar_Util.set_add x out)
=======
      (fun uu____9097  ->
         fun out  ->
           match uu____9097 with | (x,uu____9110) -> FStar_Util.set_add x out)
>>>>>>> snap
=======
      (fun uu____9097  ->
         fun out  ->
           match uu____9097 with | (x,uu____9110) -> FStar_Util.set_add x out)
>>>>>>> snap
=======
      (fun uu____9149  ->
         fun out  ->
           match uu____9149 with | (x,uu____9162) -> FStar_Util.set_add x out)
>>>>>>> snap
      bs no_names
  
let (binders_of_list : bv Prims.list -> binders) =
  fun fvs  ->
    FStar_All.pipe_right fvs
      (FStar_List.map (fun t  -> (t, FStar_Pervasives_Native.None)))
  
let (binders_of_freenames : freenames -> binders) =
  fun fvs  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9019 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____9019 binders_of_list
  
let (is_implicit : aqual -> Prims.bool) =
  fun uu___3_9030  ->
    match uu___3_9030 with
    | FStar_Pervasives_Native.Some (Implicit uu____9032) -> true
    | uu____9035 -> false
  
let (as_implicit : Prims.bool -> aqual) =
  fun uu___4_9043  ->
    if uu___4_9043
=======
=======
>>>>>>> snap
    let uu____9143 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____9143 binders_of_list
  
let (is_implicit : aqual -> Prims.bool) =
  fun uu___3_9154  ->
    match uu___3_9154 with
    | FStar_Pervasives_Native.Some (Implicit uu____9156) -> true
    | uu____9159 -> false
  
let (as_implicit : Prims.bool -> aqual) =
  fun uu___4_9167  ->
    if uu___4_9167
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
    let uu____9195 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____9195 binders_of_list
  
let (is_implicit : aqual -> Prims.bool) =
  fun uu___3_9206  ->
    match uu___3_9206 with
    | FStar_Pervasives_Native.Some (Implicit uu____9208) -> true
    | uu____9211 -> false
  
let (as_implicit : Prims.bool -> aqual) =
  fun uu___4_9219  ->
    if uu___4_9219
>>>>>>> snap
    then FStar_Pervasives_Native.Some imp_tag
    else FStar_Pervasives_Native.None
  
let (pat_bvs : pat -> bv Prims.list) =
  fun p  ->
    let rec aux b p1 =
      match p1.v with
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      | Pat_dot_term uu____9081 -> b
      | Pat_constant uu____9088 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____9091,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____9125  ->
                 match uu____9125 with | (p2,uu____9138) -> aux b1 p2) b pats
       in
    let uu____9145 = aux [] p  in
    FStar_All.pipe_left FStar_List.rev uu____9145
  
let (range_of_ropt :
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Range.range) =
  fun uu___5_9159  ->
    match uu___5_9159 with
=======
=======
>>>>>>> snap
      | Pat_dot_term uu____9205 -> b
      | Pat_constant uu____9212 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____9215,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____9249  ->
                 match uu____9249 with | (p2,uu____9262) -> aux b1 p2) b pats
       in
    let uu____9269 = aux [] p  in
    FStar_All.pipe_left FStar_List.rev uu____9269
  
let (range_of_ropt :
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Range.range) =
  fun uu___5_9283  ->
    match uu___5_9283 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      | Pat_dot_term uu____9257 -> b
      | Pat_constant uu____9264 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____9267,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____9301  ->
                 match uu____9301 with | (p2,uu____9314) -> aux b1 p2) b pats
       in
    let uu____9321 = aux [] p  in
    FStar_All.pipe_left FStar_List.rev uu____9321
  
let (range_of_ropt :
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Range.range) =
  fun uu___5_9335  ->
    match uu___5_9335 with
>>>>>>> snap
    | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange
    | FStar_Pervasives_Native.Some r -> r
  
let (gen_bv :
  Prims.string ->
    FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv)
  =
  fun s  ->
    fun r  ->
      fun t  ->
        let id1 = FStar_Ident.mk_ident (s, (range_of_ropt r))  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____9199 = FStar_Ident.next_id ()  in
        { ppname = id1; index = uu____9199; sort = t }
=======
        let uu____9323 = FStar_Ident.next_id ()  in
        { ppname = id1; index = uu____9323; sort = t }
>>>>>>> snap
=======
        let uu____9323 = FStar_Ident.next_id ()  in
        { ppname = id1; index = uu____9323; sort = t }
>>>>>>> snap
=======
        let uu____9375 = FStar_Ident.next_id ()  in
        { ppname = id1; index = uu____9375; sort = t }
>>>>>>> snap
  
let (new_bv : FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv)
  = fun ropt  -> fun t  -> gen_bv FStar_Ident.reserved_prefix ropt t 
let (freshen_bv : bv -> bv) =
  fun bv  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9222 = is_null_bv bv  in
    if uu____9222
    then
      let uu____9225 =
        let uu____9228 = range_of_bv bv  in
        FStar_Pervasives_Native.Some uu____9228  in
      new_bv uu____9225 bv.sort
    else
      (let uu___587_9231 = bv  in
       let uu____9232 = FStar_Ident.next_id ()  in
       {
         ppname = (uu___587_9231.ppname);
         index = uu____9232;
         sort = (uu___587_9231.sort)
=======
    let uu____9346 = is_null_bv bv  in
    if uu____9346
    then
      let uu____9349 =
        let uu____9352 = range_of_bv bv  in
        FStar_Pervasives_Native.Some uu____9352  in
      new_bv uu____9349 bv.sort
    else
      (let uu___605_9355 = bv  in
       let uu____9356 = FStar_Ident.next_id ()  in
       {
         ppname = (uu___605_9355.ppname);
         index = uu____9356;
         sort = (uu___605_9355.sort)
>>>>>>> snap
=======
    let uu____9346 = is_null_bv bv  in
    if uu____9346
    then
      let uu____9349 =
        let uu____9352 = range_of_bv bv  in
        FStar_Pervasives_Native.Some uu____9352  in
      new_bv uu____9349 bv.sort
    else
      (let uu___605_9355 = bv  in
       let uu____9356 = FStar_Ident.next_id ()  in
       {
         ppname = (uu___605_9355.ppname);
         index = uu____9356;
         sort = (uu___605_9355.sort)
>>>>>>> snap
=======
    let uu____9398 = is_null_bv bv  in
    if uu____9398
    then
      let uu____9401 =
        let uu____9404 = range_of_bv bv  in
        FStar_Pervasives_Native.Some uu____9404  in
      new_bv uu____9401 bv.sort
    else
      (let uu___590_9407 = bv  in
       let uu____9408 = FStar_Ident.next_id ()  in
       {
         ppname = (uu___590_9407.ppname);
         index = uu____9408;
         sort = (uu___590_9407.sort)
>>>>>>> snap
       })
  
let (freshen_binder : binder -> binder) =
  fun b  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9240 = b  in
    match uu____9240 with
    | (bv,aq) -> let uu____9247 = freshen_bv bv  in (uu____9247, aq)
=======
    let uu____9364 = b  in
    match uu____9364 with
    | (bv,aq) -> let uu____9371 = freshen_bv bv  in (uu____9371, aq)
>>>>>>> snap
=======
    let uu____9364 = b  in
    match uu____9364 with
    | (bv,aq) -> let uu____9371 = freshen_bv bv  in (uu____9371, aq)
>>>>>>> snap
=======
    let uu____9416 = b  in
    match uu____9416 with
    | (bv,aq) -> let uu____9423 = freshen_bv bv  in (uu____9423, aq)
>>>>>>> snap
  
let (new_univ_name :
  FStar_Range.range FStar_Pervasives_Native.option -> univ_name) =
  fun ropt  ->
    let id1 = FStar_Ident.next_id ()  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9262 =
      let uu____9268 =
        let uu____9270 = FStar_Util.string_of_int id1  in
        Prims.op_Hat FStar_Ident.reserved_prefix uu____9270  in
      (uu____9268, (range_of_ropt ropt))  in
    FStar_Ident.mk_ident uu____9262
=======
=======
>>>>>>> snap
    let uu____9386 =
      let uu____9392 =
        let uu____9394 = FStar_Util.string_of_int id1  in
        Prims.op_Hat FStar_Ident.reserved_prefix uu____9394  in
      (uu____9392, (range_of_ropt ropt))  in
    FStar_Ident.mk_ident uu____9386
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
    let uu____9438 =
      let uu____9444 =
        let uu____9446 = FStar_Util.string_of_int id1  in
        Prims.op_Hat FStar_Ident.reserved_prefix uu____9446  in
      (uu____9444, (range_of_ropt ropt))  in
    FStar_Ident.mk_ident uu____9438
>>>>>>> snap
  
let (mkbv : FStar_Ident.ident -> Prims.int -> term' syntax -> bv) =
  fun x  -> fun y  -> fun t  -> { ppname = x; index = y; sort = t } 
let (lbname_eq :
  (bv,FStar_Ident.lident) FStar_Util.either ->
    (bv,FStar_Ident.lident) FStar_Util.either -> Prims.bool)
  =
  fun l1  ->
    fun l2  ->
      match (l1, l2) with
      | (FStar_Util.Inl x,FStar_Util.Inl y) -> bv_eq x y
      | (FStar_Util.Inr l,FStar_Util.Inr m) -> FStar_Ident.lid_equals l m
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      | uu____9352 -> false
=======
      | uu____9476 -> false
>>>>>>> snap
=======
      | uu____9476 -> false
>>>>>>> snap
=======
      | uu____9528 -> false
>>>>>>> snap
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun fv1  ->
    fun fv2  -> FStar_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
  
let (fv_eq_lid : fv -> FStar_Ident.lident -> Prims.bool) =
  fun fv  -> fun lid  -> FStar_Ident.lid_equals (fv.fv_name).v lid 
let (set_bv_range : bv -> FStar_Range.range -> bv) =
  fun bv  ->
    fun r  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu___617_9401 = bv  in
      let uu____9402 =
        FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____9402;
        index = (uu___617_9401.index);
        sort = (uu___617_9401.sort)
=======
=======
>>>>>>> snap
      let uu___635_9525 = bv  in
      let uu____9526 =
        FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____9526;
        index = (uu___635_9525.index);
        sort = (uu___635_9525.sort)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      let uu___620_9577 = bv  in
      let uu____9578 =
        FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____9578;
        index = (uu___620_9577.index);
        sort = (uu___620_9577.sort)
>>>>>>> snap
      }
  
let (lid_as_fv :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> fv)
  =
  fun l  ->
    fun dd  ->
      fun dq  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____9424 =
          let uu____9425 = FStar_Ident.range_of_lid l  in
          withinfo l uu____9425  in
        { fv_name = uu____9424; fv_delta = dd; fv_qual = dq }
  
let (fv_to_tm : fv -> term) =
  fun fv  ->
    let uu____9432 = FStar_Ident.range_of_lid (fv.fv_name).v  in
    mk (Tm_fvar fv) FStar_Pervasives_Native.None uu____9432
=======
        let uu____9548 =
          let uu____9549 = FStar_Ident.range_of_lid l  in
          withinfo l uu____9549  in
        { fv_name = uu____9548; fv_delta = dd; fv_qual = dq }
  
let (fv_to_tm : fv -> term) =
  fun fv  ->
    let uu____9556 = FStar_Ident.range_of_lid (fv.fv_name).v  in
    mk (Tm_fvar fv) FStar_Pervasives_Native.None uu____9556
>>>>>>> snap
=======
        let uu____9548 =
          let uu____9549 = FStar_Ident.range_of_lid l  in
          withinfo l uu____9549  in
        { fv_name = uu____9548; fv_delta = dd; fv_qual = dq }
  
let (fv_to_tm : fv -> term) =
  fun fv  ->
    let uu____9556 = FStar_Ident.range_of_lid (fv.fv_name).v  in
    mk (Tm_fvar fv) FStar_Pervasives_Native.None uu____9556
>>>>>>> snap
=======
        let uu____9600 =
          let uu____9601 = FStar_Ident.range_of_lid l  in
          withinfo l uu____9601  in
        { fv_name = uu____9600; fv_delta = dd; fv_qual = dq }
  
let (fv_to_tm : fv -> term) =
  fun fv  ->
    let uu____9608 = FStar_Ident.range_of_lid (fv.fv_name).v  in
    mk (Tm_fvar fv) FStar_Pervasives_Native.None uu____9608
>>>>>>> snap
  
let (fvar :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> term)
  =
  fun l  ->
    fun dd  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      fun dq  -> let uu____9453 = lid_as_fv l dd dq  in fv_to_tm uu____9453
=======
      fun dq  -> let uu____9577 = lid_as_fv l dd dq  in fv_to_tm uu____9577
>>>>>>> snap
=======
      fun dq  -> let uu____9577 = lid_as_fv l dd dq  in fv_to_tm uu____9577
>>>>>>> snap
=======
      fun dq  -> let uu____9629 = lid_as_fv l dd dq  in fv_to_tm uu____9629
>>>>>>> snap
  
let (lid_of_fv : fv -> FStar_Ident.lid) = fun fv  -> (fv.fv_name).v 
let (range_of_fv : fv -> FStar_Range.range) =
  fun fv  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9466 = lid_of_fv fv  in FStar_Ident.range_of_lid uu____9466
=======
    let uu____9590 = lid_of_fv fv  in FStar_Ident.range_of_lid uu____9590
>>>>>>> snap
=======
    let uu____9590 = lid_of_fv fv  in FStar_Ident.range_of_lid uu____9590
>>>>>>> snap
=======
    let uu____9642 = lid_of_fv fv  in FStar_Ident.range_of_lid uu____9642
>>>>>>> snap
  
let (set_range_of_fv : fv -> FStar_Range.range -> fv) =
  fun fv  ->
    fun r  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu___630_9478 = fv  in
      let uu____9479 =
        let uu___632_9480 = fv.fv_name  in
        let uu____9481 =
          let uu____9482 = lid_of_fv fv  in
          FStar_Ident.set_lid_range uu____9482 r  in
        { v = uu____9481; p = (uu___632_9480.p) }  in
      {
        fv_name = uu____9479;
        fv_delta = (uu___630_9478.fv_delta);
        fv_qual = (uu___630_9478.fv_qual)
=======
=======
>>>>>>> snap
      let uu___648_9602 = fv  in
      let uu____9603 =
        let uu___650_9604 = fv.fv_name  in
        let uu____9605 =
          let uu____9606 = lid_of_fv fv  in
          FStar_Ident.set_lid_range uu____9606 r  in
        { v = uu____9605; p = (uu___650_9604.p) }  in
      {
        fv_name = uu____9603;
        fv_delta = (uu___648_9602.fv_delta);
        fv_qual = (uu___648_9602.fv_qual)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      let uu___633_9654 = fv  in
      let uu____9655 =
        let uu___635_9656 = fv.fv_name  in
        let uu____9657 =
          let uu____9658 = lid_of_fv fv  in
          FStar_Ident.set_lid_range uu____9658 r  in
        { v = uu____9657; p = (uu___635_9656.p) }  in
      {
        fv_name = uu____9655;
        fv_delta = (uu___633_9654.fv_delta);
        fv_qual = (uu___633_9654.fv_qual)
>>>>>>> snap
      }
  
let (has_simple_attribute : term Prims.list -> Prims.string -> Prims.bool) =
  fun l  ->
    fun s  ->
      FStar_List.existsb
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        (fun uu___6_9508  ->
           match uu___6_9508 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____9513));
               pos = uu____9514; vars = uu____9515;_} when data = s -> true
           | uu____9522 -> false) l
=======
=======
>>>>>>> snap
        (fun uu___6_9632  ->
           match uu___6_9632 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____9637));
               pos = uu____9638; vars = uu____9639;_} when data = s -> true
           | uu____9646 -> false) l
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
        (fun uu___6_9684  ->
           match uu___6_9684 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____9689));
               pos = uu____9690; vars = uu____9691;_} when data = s -> true
           | uu____9698 -> false) l
>>>>>>> snap
  
let rec (eq_pat : pat -> pat -> Prims.bool) =
  fun p1  ->
    fun p2  ->
      match ((p1.v), (p2.v)) with
      | (Pat_constant c1,Pat_constant c2) -> FStar_Const.eq_const c1 c2
      | (Pat_cons (fv1,as1),Pat_cons (fv2,as2)) ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____9581 = fv_eq fv1 fv2  in
          if uu____9581
          then
            let uu____9586 = FStar_List.zip as1 as2  in
            FStar_All.pipe_right uu____9586
              (FStar_List.for_all
                 (fun uu____9653  ->
                    match uu____9653 with
                    | ((p11,b1),(p21,b2)) -> (b1 = b2) && (eq_pat p11 p21)))
          else false
      | (Pat_var uu____9691,Pat_var uu____9692) -> true
      | (Pat_wild uu____9694,Pat_wild uu____9695) -> true
      | (Pat_dot_term (bv1,t1),Pat_dot_term (bv2,t2)) -> true
      | (uu____9710,uu____9711) -> false
=======
          let uu____9705 = fv_eq fv1 fv2  in
          if uu____9705
          then
            let uu____9710 = FStar_List.zip as1 as2  in
            FStar_All.pipe_right uu____9710
              (FStar_List.for_all
                 (fun uu____9777  ->
                    match uu____9777 with
                    | ((p11,b1),(p21,b2)) -> (b1 = b2) && (eq_pat p11 p21)))
          else false
      | (Pat_var uu____9815,Pat_var uu____9816) -> true
      | (Pat_wild uu____9818,Pat_wild uu____9819) -> true
      | (Pat_dot_term (bv1,t1),Pat_dot_term (bv2,t2)) -> true
      | (uu____9834,uu____9835) -> false
>>>>>>> snap
=======
          let uu____9705 = fv_eq fv1 fv2  in
          if uu____9705
          then
            let uu____9710 = FStar_List.zip as1 as2  in
            FStar_All.pipe_right uu____9710
              (FStar_List.for_all
                 (fun uu____9777  ->
                    match uu____9777 with
                    | ((p11,b1),(p21,b2)) -> (b1 = b2) && (eq_pat p11 p21)))
          else false
      | (Pat_var uu____9815,Pat_var uu____9816) -> true
      | (Pat_wild uu____9818,Pat_wild uu____9819) -> true
      | (Pat_dot_term (bv1,t1),Pat_dot_term (bv2,t2)) -> true
      | (uu____9834,uu____9835) -> false
>>>>>>> snap
=======
          let uu____9757 = fv_eq fv1 fv2  in
          if uu____9757
          then
            let uu____9762 = FStar_List.zip as1 as2  in
            FStar_All.pipe_right uu____9762
              (FStar_List.for_all
                 (fun uu____9829  ->
                    match uu____9829 with
                    | ((p11,b1),(p21,b2)) -> (b1 = b2) && (eq_pat p11 p21)))
          else false
      | (Pat_var uu____9867,Pat_var uu____9868) -> true
      | (Pat_wild uu____9870,Pat_wild uu____9871) -> true
      | (Pat_dot_term (bv1,t1),Pat_dot_term (bv2,t2)) -> true
      | (uu____9886,uu____9887) -> false
>>>>>>> snap
  
let (delta_constant : delta_depth) = Delta_constant_at_level Prims.int_zero 
let (delta_equational : delta_depth) =
  Delta_equational_at_level Prims.int_zero 
let (fvconst : FStar_Ident.lident -> fv) =
  fun l  -> lid_as_fv l delta_constant FStar_Pervasives_Native.None 
let (tconst : FStar_Ident.lident -> term) =
  fun l  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9729 =
      let uu____9736 = let uu____9737 = fvconst l  in Tm_fvar uu____9737  in
      mk uu____9736  in
    uu____9729 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tabbrev : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9744 =
      let uu____9751 =
        let uu____9752 =
          lid_as_fv l (Delta_constant_at_level Prims.int_one)
            FStar_Pervasives_Native.None
           in
        Tm_fvar uu____9752  in
      mk uu____9751  in
    uu____9744 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tdataconstr : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9760 =
      lid_as_fv l delta_constant (FStar_Pervasives_Native.Some Data_ctor)  in
    fv_to_tm uu____9760
=======
=======
>>>>>>> snap
    let uu____9853 =
      let uu____9860 = let uu____9861 = fvconst l  in Tm_fvar uu____9861  in
      mk uu____9860  in
    uu____9853 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tabbrev : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9868 =
      let uu____9875 =
        let uu____9876 =
          lid_as_fv l (Delta_constant_at_level Prims.int_one)
            FStar_Pervasives_Native.None
           in
        Tm_fvar uu____9876  in
      mk uu____9875  in
    uu____9868 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tdataconstr : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9884 =
      lid_as_fv l delta_constant (FStar_Pervasives_Native.Some Data_ctor)  in
    fv_to_tm uu____9884
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
    let uu____9905 =
      let uu____9912 = let uu____9913 = fvconst l  in Tm_fvar uu____9913  in
      mk uu____9912  in
    uu____9905 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tabbrev : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9920 =
      let uu____9927 =
        let uu____9928 =
          lid_as_fv l (Delta_constant_at_level Prims.int_one)
            FStar_Pervasives_Native.None
           in
        Tm_fvar uu____9928  in
      mk uu____9927  in
    uu____9920 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tdataconstr : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9936 =
      lid_as_fv l delta_constant (FStar_Pervasives_Native.Some Data_ctor)  in
    fv_to_tm uu____9936
>>>>>>> snap
  
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
<<<<<<< HEAD
let (t_tactic_unit : term) =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
  let uu____9779 =
    let uu____9784 =
      let uu____9785 = tabbrev FStar_Parser_Const.tactic_lid  in
      mk_Tm_uinst uu____9785 [U_zero]  in
    let uu____9786 = let uu____9787 = as_arg t_unit  in [uu____9787]  in
    mk_Tm_app uu____9784 uu____9786  in
  uu____9779 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (t_list_of : term -> term) =
  fun t  ->
    let uu____9818 =
      let uu____9823 =
        let uu____9824 = tabbrev FStar_Parser_Const.list_lid  in
        mk_Tm_uinst uu____9824 [U_zero]  in
      let uu____9825 = let uu____9826 = as_arg t  in [uu____9826]  in
      mk_Tm_app uu____9823 uu____9825  in
    uu____9818 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_option_of : term -> term) =
  fun t  ->
    let uu____9857 =
      let uu____9862 =
        let uu____9863 = tabbrev FStar_Parser_Const.option_lid  in
        mk_Tm_uinst uu____9863 [U_zero]  in
      let uu____9864 = let uu____9865 = as_arg t  in [uu____9865]  in
      mk_Tm_app uu____9862 uu____9864  in
    uu____9857 FStar_Pervasives_Native.None FStar_Range.dummyRange
=======
=======
>>>>>>> snap
  let uu____9903 =
    let uu____9908 =
      let uu____9909 = tabbrev FStar_Parser_Const.tactic_lid  in
      mk_Tm_uinst uu____9909 [U_zero]  in
    let uu____9910 = let uu____9911 = as_arg t_unit  in [uu____9911]  in
    mk_Tm_app uu____9908 uu____9910  in
  uu____9903 FStar_Pervasives_Native.None FStar_Range.dummyRange 
=======
  let uu____9904 =
    let uu____9909 =
      let uu____9910 = tabbrev FStar_Parser_Const.tactic_lid  in
      mk_Tm_uinst uu____9910 [U_zero]  in
    let uu____9911 = let uu____9912 = as_arg t_unit  in [uu____9912]  in
    mk_Tm_app uu____9909 uu____9911  in
  uu____9904 FStar_Pervasives_Native.None FStar_Range.dummyRange 
>>>>>>> snap
=======
let (t_tac_of : term -> term -> term) =
  fun a  ->
    fun b  ->
<<<<<<< HEAD
      let uu____9914 =
        let uu____9919 =
          let uu____9920 = tabbrev FStar_Parser_Const.tac_lid  in
          mk_Tm_uinst uu____9920 [U_unknown]  in
        let uu____9921 =
          let uu____9922 = as_arg a  in
          let uu____9931 = let uu____9942 = as_arg b  in [uu____9942]  in
          uu____9922 :: uu____9931  in
        mk_Tm_app uu____9919 uu____9921  in
      uu____9914 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_tactic_of : term -> term) =
  fun t  ->
    let uu____9981 =
      let uu____9986 =
        let uu____9987 = tabbrev FStar_Parser_Const.tactic_lid  in
        mk_Tm_uinst uu____9987 [U_unknown]  in
      let uu____9988 = let uu____9989 = as_arg t  in [uu____9989]  in
      mk_Tm_app uu____9986 uu____9988  in
    uu____9981 FStar_Pervasives_Native.None FStar_Range.dummyRange
=======
      let uu____9966 =
        let uu____9971 =
          let uu____9972 = tabbrev FStar_Parser_Const.tac_lid  in
          mk_Tm_uinst uu____9972 [U_unknown]  in
        let uu____9973 =
          let uu____9974 = as_arg a  in
          let uu____9983 = let uu____9994 = as_arg b  in [uu____9994]  in
          uu____9974 :: uu____9983  in
        mk_Tm_app uu____9971 uu____9973  in
      uu____9966 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_tactic_of : term -> term) =
  fun t  ->
    let uu____10033 =
      let uu____10038 =
        let uu____10039 = tabbrev FStar_Parser_Const.tactic_lid  in
        mk_Tm_uinst uu____10039 [U_unknown]  in
      let uu____10040 = let uu____10041 = as_arg t  in [uu____10041]  in
      mk_Tm_app uu____10038 uu____10040  in
    uu____10033 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
  
let (t_tactic_unit : term) = t_tactic_of t_unit 
>>>>>>> snap
let (t_list_of : term -> term) =
  fun t  ->
<<<<<<< HEAD
    let uu____10021 =
      let uu____10026 =
        let uu____10027 = tabbrev FStar_Parser_Const.list_lid  in
        mk_Tm_uinst uu____10027 [U_zero]  in
      let uu____10028 = let uu____10029 = as_arg t  in [uu____10029]  in
      mk_Tm_app uu____10026 uu____10028  in
    uu____10021 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_option_of : term -> term) =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9981 =
      let uu____9986 =
        let uu____9987 = tabbrev FStar_Parser_Const.option_lid  in
        mk_Tm_uinst uu____9987 [U_zero]  in
      let uu____9988 = let uu____9989 = as_arg t  in [uu____9989]  in
      mk_Tm_app uu____9986 uu____9988  in
    uu____9981 FStar_Pervasives_Native.None FStar_Range.dummyRange
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
    let uu____9982 =
      let uu____9987 =
        let uu____9988 = tabbrev FStar_Parser_Const.option_lid  in
        mk_Tm_uinst uu____9988 [U_zero]  in
      let uu____9989 = let uu____9990 = as_arg t  in [uu____9990]  in
      mk_Tm_app uu____9987 uu____9989  in
    uu____9982 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
=======
    let uu____10060 =
      let uu____10065 =
        let uu____10066 = tabbrev FStar_Parser_Const.option_lid  in
        mk_Tm_uinst uu____10066 [U_zero]  in
      let uu____10067 = let uu____10068 = as_arg t  in [uu____10068]  in
      mk_Tm_app uu____10065 uu____10067  in
    uu____10060 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
=======
    let uu____10073 =
      let uu____10078 =
        let uu____10079 = tabbrev FStar_Parser_Const.list_lid  in
        mk_Tm_uinst uu____10079 [U_zero]  in
      let uu____10080 = let uu____10081 = as_arg t  in [uu____10081]  in
      mk_Tm_app uu____10078 uu____10080  in
    uu____10073 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_option_of : term -> term) =
  fun t  ->
    let uu____10112 =
      let uu____10117 =
        let uu____10118 = tabbrev FStar_Parser_Const.option_lid  in
        mk_Tm_uinst uu____10118 [U_zero]  in
      let uu____10119 = let uu____10120 = as_arg t  in [uu____10120]  in
      mk_Tm_app uu____10117 uu____10119  in
    uu____10112 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
  
let (t_tuple2_of : term -> term -> term) =
  fun t1  ->
    fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____9901 =
        let uu____9906 =
          let uu____9907 = tabbrev FStar_Parser_Const.lid_tuple2  in
          mk_Tm_uinst uu____9907 [U_zero; U_zero]  in
        let uu____9908 =
          let uu____9909 = as_arg t1  in
          let uu____9918 = let uu____9929 = as_arg t2  in [uu____9929]  in
          uu____9909 :: uu____9918  in
        mk_Tm_app uu____9906 uu____9908  in
      uu____9901 FStar_Pervasives_Native.None FStar_Range.dummyRange
=======
=======
>>>>>>> snap
      let uu____10025 =
        let uu____10030 =
          let uu____10031 = tabbrev FStar_Parser_Const.lid_tuple2  in
          mk_Tm_uinst uu____10031 [U_zero; U_zero]  in
        let uu____10032 =
          let uu____10033 = as_arg t1  in
          let uu____10042 = let uu____10053 = as_arg t2  in [uu____10053]  in
          uu____10033 :: uu____10042  in
        mk_Tm_app uu____10030 uu____10032  in
      uu____10025 FStar_Pervasives_Native.None FStar_Range.dummyRange
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      let uu____10026 =
        let uu____10031 =
          let uu____10032 = tabbrev FStar_Parser_Const.lid_tuple2  in
          mk_Tm_uinst uu____10032 [U_zero; U_zero]  in
        let uu____10033 =
          let uu____10034 = as_arg t1  in
          let uu____10043 = let uu____10054 = as_arg t2  in [uu____10054]  in
          uu____10034 :: uu____10043  in
        mk_Tm_app uu____10031 uu____10033  in
      uu____10026 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
=======
      let uu____10104 =
        let uu____10109 =
          let uu____10110 = tabbrev FStar_Parser_Const.lid_tuple2  in
          mk_Tm_uinst uu____10110 [U_zero; U_zero]  in
        let uu____10111 =
          let uu____10112 = as_arg t1  in
          let uu____10121 = let uu____10132 = as_arg t2  in [uu____10132]  in
          uu____10112 :: uu____10121  in
        mk_Tm_app uu____10109 uu____10111  in
      uu____10104 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
=======
      let uu____10156 =
        let uu____10161 =
          let uu____10162 = tabbrev FStar_Parser_Const.lid_tuple2  in
          mk_Tm_uinst uu____10162 [U_zero; U_zero]  in
        let uu____10163 =
          let uu____10164 = as_arg t1  in
          let uu____10173 = let uu____10184 = as_arg t2  in [uu____10184]  in
          uu____10164 :: uu____10173  in
        mk_Tm_app uu____10161 uu____10163  in
      uu____10156 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
  
let (t_either_of : term -> term -> term) =
  fun t1  ->
    fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____9973 =
        let uu____9978 =
          let uu____9979 = tabbrev FStar_Parser_Const.either_lid  in
          mk_Tm_uinst uu____9979 [U_zero; U_zero]  in
        let uu____9980 =
          let uu____9981 = as_arg t1  in
          let uu____9990 = let uu____10001 = as_arg t2  in [uu____10001]  in
          uu____9981 :: uu____9990  in
        mk_Tm_app uu____9978 uu____9980  in
      uu____9973 FStar_Pervasives_Native.None FStar_Range.dummyRange
=======
=======
>>>>>>> snap
      let uu____10097 =
        let uu____10102 =
          let uu____10103 = tabbrev FStar_Parser_Const.either_lid  in
          mk_Tm_uinst uu____10103 [U_zero; U_zero]  in
        let uu____10104 =
          let uu____10105 = as_arg t1  in
          let uu____10114 = let uu____10125 = as_arg t2  in [uu____10125]  in
          uu____10105 :: uu____10114  in
        mk_Tm_app uu____10102 uu____10104  in
      uu____10097 FStar_Pervasives_Native.None FStar_Range.dummyRange
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
=======
      let uu____10098 =
        let uu____10103 =
          let uu____10104 = tabbrev FStar_Parser_Const.either_lid  in
          mk_Tm_uinst uu____10104 [U_zero; U_zero]  in
        let uu____10105 =
          let uu____10106 = as_arg t1  in
          let uu____10115 = let uu____10126 = as_arg t2  in [uu____10126]  in
          uu____10106 :: uu____10115  in
        mk_Tm_app uu____10103 uu____10105  in
      uu____10098 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
=======
      let uu____10176 =
        let uu____10181 =
          let uu____10182 = tabbrev FStar_Parser_Const.either_lid  in
          mk_Tm_uinst uu____10182 [U_zero; U_zero]  in
        let uu____10183 =
          let uu____10184 = as_arg t1  in
          let uu____10193 = let uu____10204 = as_arg t2  in [uu____10204]  in
          uu____10184 :: uu____10193  in
        mk_Tm_app uu____10181 uu____10183  in
      uu____10176 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
=======
      let uu____10228 =
        let uu____10233 =
          let uu____10234 = tabbrev FStar_Parser_Const.either_lid  in
          mk_Tm_uinst uu____10234 [U_zero; U_zero]  in
        let uu____10235 =
          let uu____10236 = as_arg t1  in
          let uu____10245 = let uu____10256 = as_arg t2  in [uu____10256]  in
          uu____10236 :: uu____10245  in
        mk_Tm_app uu____10233 uu____10235  in
      uu____10228 FStar_Pervasives_Native.None FStar_Range.dummyRange
>>>>>>> snap
  
let (unit_const : term) =
  mk (Tm_constant FStar_Const.Const_unit) FStar_Pervasives_Native.None
    FStar_Range.dummyRange
  