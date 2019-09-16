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
    match projectee with | SetOptions _0 -> true | uu____175 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____200 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____231 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____258 -> false
  
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | RestartSolver  -> true | uu____269 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____280 -> false
  
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
    match projectee with | ET_abstract  -> true | uu____320 -> false
  
let (uu___is_ET_fun : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_fun _0 -> true | uu____336 -> false
  
let (__proj__ET_fun__item___0 : emb_typ -> (emb_typ * emb_typ)) =
  fun projectee  -> match projectee with | ET_fun _0 -> _0 
let (uu___is_ET_app : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_app _0 -> true | uu____374 -> false
  
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
    match projectee with | U_zero  -> true | uu____485 -> false
  
let (uu___is_U_succ : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_succ _0 -> true | uu____497 -> false
  
let (__proj__U_succ__item___0 : universe -> universe) =
  fun projectee  -> match projectee with | U_succ _0 -> _0 
let (uu___is_U_max : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_max _0 -> true | uu____518 -> false
  
let (__proj__U_max__item___0 : universe -> universe Prims.list) =
  fun projectee  -> match projectee with | U_max _0 -> _0 
let (uu___is_U_bvar : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_bvar _0 -> true | uu____544 -> false
  
let (__proj__U_bvar__item___0 : universe -> Prims.int) =
  fun projectee  -> match projectee with | U_bvar _0 -> _0 
let (uu___is_U_name : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_name _0 -> true | uu____566 -> false
  
let (__proj__U_name__item___0 : universe -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | U_name _0 -> _0 
let (uu___is_U_unif : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_unif _0 -> true | uu____593 -> false
  
let (__proj__U_unif__item___0 :
  universe ->
    (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar *
      version))
  = fun projectee  -> match projectee with | U_unif _0 -> _0 
let (uu___is_U_unknown : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_unknown  -> true | uu____635 -> false
  
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
    match projectee with | Quote_static  -> true | uu____658 -> false
  
let (uu___is_Quote_dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote_dynamic  -> true | uu____669 -> false
  
type maybe_set_use_range =
  | NoUseRange 
  | SomeUseRange of FStar_Range.range [@@deriving yojson,show,yojson,show]
let (uu___is_NoUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUseRange  -> true | uu____685 -> false
  
let (uu___is_SomeUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee  ->
    match projectee with | SomeUseRange _0 -> true | uu____697 -> false
  
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
    | uu____734 -> false
  
let (__proj__Delta_constant_at_level__item___0 : delta_depth -> Prims.int) =
  fun projectee  -> match projectee with | Delta_constant_at_level _0 -> _0 
let (uu___is_Delta_equational_at_level : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Delta_equational_at_level _0 -> true
    | uu____757 -> false
  
let (__proj__Delta_equational_at_level__item___0 : delta_depth -> Prims.int)
  =
  fun projectee  -> match projectee with | Delta_equational_at_level _0 -> _0 
let (uu___is_Delta_abstract : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta_abstract _0 -> true | uu____779 -> false
  
let (__proj__Delta_abstract__item___0 : delta_depth -> delta_depth) =
  fun projectee  -> match projectee with | Delta_abstract _0 -> _0 
type should_check_uvar =
  | Allow_unresolved 
  | Allow_untyped 
  | Strict [@@deriving yojson,show,yojson,show]
let (uu___is_Allow_unresolved : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Allow_unresolved  -> true | uu____797 -> false
  
let (uu___is_Allow_untyped : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Allow_untyped  -> true | uu____808 -> false
  
let (uu___is_Strict : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Strict  -> true | uu____819 -> false
  
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
    match projectee with | Tm_bvar _0 -> true | uu____1709 -> false
  
let (__proj__Tm_bvar__item___0 : term' -> bv) =
  fun projectee  -> match projectee with | Tm_bvar _0 -> _0 
let (uu___is_Tm_name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_name _0 -> true | uu____1728 -> false
  
let (__proj__Tm_name__item___0 : term' -> bv) =
  fun projectee  -> match projectee with | Tm_name _0 -> _0 
let (uu___is_Tm_fvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_fvar _0 -> true | uu____1747 -> false
  
let (__proj__Tm_fvar__item___0 : term' -> fv) =
  fun projectee  -> match projectee with | Tm_fvar _0 -> _0 
let (uu___is_Tm_uinst : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_uinst _0 -> true | uu____1772 -> false
  
let (__proj__Tm_uinst__item___0 : term' -> (term' syntax * universes)) =
  fun projectee  -> match projectee with | Tm_uinst _0 -> _0 
let (uu___is_Tm_constant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_constant _0 -> true | uu____1809 -> false
  
let (__proj__Tm_constant__item___0 : term' -> sconst) =
  fun projectee  -> match projectee with | Tm_constant _0 -> _0 
let (uu___is_Tm_type : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_type _0 -> true | uu____1828 -> false
  
let (__proj__Tm_type__item___0 : term' -> universe) =
  fun projectee  -> match projectee with | Tm_type _0 -> _0 
let (uu___is_Tm_abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_abs _0 -> true | uu____1865 -> false
  
let (__proj__Tm_abs__item___0 :
  term' ->
    ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * term'
      syntax * residual_comp FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tm_abs _0 -> _0 
let (uu___is_Tm_arrow : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_arrow _0 -> true | uu____1952 -> false
  
let (__proj__Tm_arrow__item___0 :
  term' ->
    ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * comp'
      syntax))
  = fun projectee  -> match projectee with | Tm_arrow _0 -> _0 
let (uu___is_Tm_refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_refine _0 -> true | uu____2019 -> false
  
let (__proj__Tm_refine__item___0 : term' -> (bv * term' syntax)) =
  fun projectee  -> match projectee with | Tm_refine _0 -> _0 
let (uu___is_Tm_app : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_app _0 -> true | uu____2072 -> false
  
let (__proj__Tm_app__item___0 :
  term' ->
    (term' syntax * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee  -> match projectee with | Tm_app _0 -> _0 
let (uu___is_Tm_match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_match _0 -> true | uu____2161 -> false
  
let (__proj__Tm_match__item___0 :
  term' ->
    (term' syntax * (pat' withinfo_t * term' syntax
      FStar_Pervasives_Native.option * term' syntax) Prims.list))
  = fun projectee  -> match projectee with | Tm_match _0 -> _0 
let (uu___is_Tm_ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_ascribed _0 -> true | uu____2272 -> false
  
let (__proj__Tm_ascribed__item___0 :
  term' ->
    (term' syntax * ((term' syntax,comp' syntax) FStar_Util.either * term'
      syntax FStar_Pervasives_Native.option) * FStar_Ident.lident
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tm_ascribed _0 -> _0 
let (uu___is_Tm_let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_let _0 -> true | uu____2382 -> false
  
let (__proj__Tm_let__item___0 :
  term' -> ((Prims.bool * letbinding Prims.list) * term' syntax)) =
  fun projectee  -> match projectee with | Tm_let _0 -> _0 
let (uu___is_Tm_uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_uvar _0 -> true | uu____2452 -> false
  
let (__proj__Tm_uvar__item___0 :
  term' ->
    (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range)))
  = fun projectee  -> match projectee with | Tm_uvar _0 -> _0 
let (uu___is_Tm_delayed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_delayed _0 -> true | uu____2529 -> false
  
let (__proj__Tm_delayed__item___0 :
  term' ->
    ((term' syntax * (subst_elt Prims.list Prims.list * maybe_set_use_range))
      * term' syntax memo))
  = fun projectee  -> match projectee with | Tm_delayed _0 -> _0 
let (uu___is_Tm_meta : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_meta _0 -> true | uu____2620 -> false
  
let (__proj__Tm_meta__item___0 : term' -> (term' syntax * metadata)) =
  fun projectee  -> match projectee with | Tm_meta _0 -> _0 
let (uu___is_Tm_lazy : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_lazy _0 -> true | uu____2657 -> false
  
let (__proj__Tm_lazy__item___0 : term' -> lazyinfo) =
  fun projectee  -> match projectee with | Tm_lazy _0 -> _0 
let (uu___is_Tm_quoted : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_quoted _0 -> true | uu____2682 -> false
  
let (__proj__Tm_quoted__item___0 : term' -> (term' syntax * quoteinfo)) =
  fun projectee  -> match projectee with | Tm_quoted _0 -> _0 
let (uu___is_Tm_unknown : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_unknown  -> true | uu____2718 -> false
  
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
    match projectee with | Pat_constant _0 -> true | uu____3152 -> false
  
let (__proj__Pat_constant__item___0 : pat' -> sconst) =
  fun projectee  -> match projectee with | Pat_constant _0 -> _0 
let (uu___is_Pat_cons : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_cons _0 -> true | uu____3184 -> false
  
let (__proj__Pat_cons__item___0 :
  pat' -> (fv * (pat' withinfo_t * Prims.bool) Prims.list)) =
  fun projectee  -> match projectee with | Pat_cons _0 -> _0 
let (uu___is_Pat_var : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_var _0 -> true | uu____3242 -> false
  
let (__proj__Pat_var__item___0 : pat' -> bv) =
  fun projectee  -> match projectee with | Pat_var _0 -> _0 
let (uu___is_Pat_wild : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_wild _0 -> true | uu____3261 -> false
  
let (__proj__Pat_wild__item___0 : pat' -> bv) =
  fun projectee  -> match projectee with | Pat_wild _0 -> _0 
let (uu___is_Pat_dot_term : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_dot_term _0 -> true | uu____3286 -> false
  
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
    match projectee with | Total _0 -> true | uu____3749 -> false
  
let (__proj__Total__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Total _0 -> _0 
let (uu___is_GTotal : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTotal _0 -> true | uu____3800 -> false
  
let (__proj__GTotal__item___0 :
  comp' -> (term' syntax * universe FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | GTotal _0 -> _0 
let (uu___is_Comp : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____3843 -> false
  
let (__proj__Comp__item___0 : comp' -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____3861 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____3872 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____3883 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____3894 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____3905 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____3916 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____3927 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____3938 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____3949 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____3963 -> false
  
let (__proj__DECREASES__item___0 : cflag -> term' syntax) =
  fun projectee  -> match projectee with | DECREASES _0 -> _0 
let (uu___is_Meta_pattern : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_pattern _0 -> true | uu____4008 -> false
  
let (__proj__Meta_pattern__item___0 :
  metadata ->
    (term' syntax Prims.list * (term' syntax * arg_qualifier
      FStar_Pervasives_Native.option) Prims.list Prims.list))
  = fun projectee  -> match projectee with | Meta_pattern _0 -> _0 
let (uu___is_Meta_named : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_named _0 -> true | uu____4087 -> false
  
let (__proj__Meta_named__item___0 : metadata -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Meta_named _0 -> _0 
let (uu___is_Meta_labeled : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_labeled _0 -> true | uu____4114 -> false
  
let (__proj__Meta_labeled__item___0 :
  metadata -> (Prims.string * FStar_Range.range * Prims.bool)) =
  fun projectee  -> match projectee with | Meta_labeled _0 -> _0 
let (uu___is_Meta_desugared : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_desugared _0 -> true | uu____4157 -> false
  
let (__proj__Meta_desugared__item___0 : metadata -> meta_source_info) =
  fun projectee  -> match projectee with | Meta_desugared _0 -> _0 
let (uu___is_Meta_monadic : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_monadic _0 -> true | uu____4182 -> false
  
let (__proj__Meta_monadic__item___0 :
  metadata -> (monad_name * term' syntax)) =
  fun projectee  -> match projectee with | Meta_monadic _0 -> _0 
let (uu___is_Meta_monadic_lift : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_monadic_lift _0 -> true | uu____4227 -> false
  
let (__proj__Meta_monadic_lift__item___0 :
  metadata -> (monad_name * monad_name * term' syntax)) =
  fun projectee  -> match projectee with | Meta_monadic_lift _0 -> _0 
let (uu___is_Sequence : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sequence  -> true | uu____4269 -> false
  
let (uu___is_Primop : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primop  -> true | uu____4280 -> false
  
let (uu___is_Masked_effect : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Masked_effect  -> true | uu____4291 -> false
  
let (uu___is_Meta_smt_pat : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_smt_pat  -> true | uu____4302 -> false
  
let (uu___is_Data_ctor : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Data_ctor  -> true | uu____4313 -> false
  
let (uu___is_Record_projector : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_projector _0 -> true | uu____4329 -> false
  
let (__proj__Record_projector__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Record_projector _0 -> _0 
let (uu___is_Record_ctor : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_ctor _0 -> true | uu____4366 -> false
  
let (__proj__Record_ctor__item___0 :
  fv_qual -> (FStar_Ident.lident * FStar_Ident.ident Prims.list)) =
  fun projectee  -> match projectee with | Record_ctor _0 -> _0 
let (uu___is_DB : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | DB _0 -> true | uu____4408 -> false
  
let (__proj__DB__item___0 : subst_elt -> (Prims.int * bv)) =
  fun projectee  -> match projectee with | DB _0 -> _0 
let (uu___is_NM : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | NM _0 -> true | uu____4447 -> false
  
let (__proj__NM__item___0 : subst_elt -> (bv * Prims.int)) =
  fun projectee  -> match projectee with | NM _0 -> _0 
let (uu___is_NT : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | NT _0 -> true | uu____4487 -> false
  
let (__proj__NT__item___0 : subst_elt -> (bv * term' syntax)) =
  fun projectee  -> match projectee with | NT _0 -> _0 
let (uu___is_UN : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UN _0 -> true | uu____4529 -> false
  
let (__proj__UN__item___0 : subst_elt -> (Prims.int * universe)) =
  fun projectee  -> match projectee with | UN _0 -> _0 
let (uu___is_UD : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UD _0 -> true | uu____4568 -> false
  
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
    match projectee with | BadLazy  -> true | uu____4939 -> false
  
let (uu___is_Lazy_bv : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_bv  -> true | uu____4950 -> false
  
let (uu___is_Lazy_binder : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_binder  -> true | uu____4961 -> false
  
let (uu___is_Lazy_fvar : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_fvar  -> true | uu____4972 -> false
  
let (uu___is_Lazy_comp : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_comp  -> true | uu____4983 -> false
  
let (uu___is_Lazy_env : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_env  -> true | uu____4994 -> false
  
let (uu___is_Lazy_proofstate : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_proofstate  -> true | uu____5005 -> false
  
let (uu___is_Lazy_goal : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_goal  -> true | uu____5016 -> false
  
let (uu___is_Lazy_sigelt : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_sigelt  -> true | uu____5027 -> false
  
let (uu___is_Lazy_uvar : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_uvar  -> true | uu____5038 -> false
  
let (uu___is_Lazy_embedding : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_embedding _0 -> true | uu____5058 -> false
  
let (__proj__Lazy_embedding__item___0 :
  lazy_kind -> (emb_typ * term' syntax FStar_Common.thunk)) =
  fun projectee  -> match projectee with | Lazy_embedding _0 -> _0 
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____5101 -> false
  
let (__proj__Binding_var__item___0 : binding -> bv) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____5132 -> false
  
let (__proj__Binding_lid__item___0 :
  binding -> (FStar_Ident.lident * (univ_name Prims.list * term' syntax))) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____5187 -> false
  
let (__proj__Binding_univ__item___0 : binding -> univ_name) =
  fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit _0 -> true | uu____5207 -> false
  
let (__proj__Implicit__item___0 : arg_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Implicit _0 -> _0 
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____5231 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term' syntax) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____5255 -> false
  
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
type lcomp =
  {
  eff_name: FStar_Ident.lident ;
  res_typ: typ ;
  cflags: cflag Prims.list ;
  comp_thunk: (unit -> comp,comp) FStar_Util.either FStar_ST.ref }
let (__proj__Mklcomp__item__eff_name : lcomp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> eff_name
  
let (__proj__Mklcomp__item__res_typ : lcomp -> typ) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> res_typ
  
let (__proj__Mklcomp__item__cflags : lcomp -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> cflags
  
let (__proj__Mklcomp__item__comp_thunk :
  lcomp -> (unit -> comp,comp) FStar_Util.either FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> comp_thunk
  
let (lazy_chooser :
  (lazy_kind -> lazyinfo -> term) FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (mk_lcomp :
  FStar_Ident.lident -> typ -> cflag Prims.list -> (unit -> comp) -> lcomp) =
  fun eff_name  ->
    fun res_typ  ->
      fun cflags  ->
        fun comp_thunk  ->
          let uu____5615 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____5615 }
  
let (lcomp_comp : lcomp -> comp) =
  fun lc  ->
    let uu____5641 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____5641 with
    | FStar_Util.Inl thunk ->
        let c = thunk ()  in
        (FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr c); c)
    | FStar_Util.Inr c -> c
  
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
    match projectee with | Assumption  -> true | uu____5794 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____5805 -> false 
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____5816 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____5827 -> false
  
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____5838 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____5849 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____5860 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____5871 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____5882 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____5893 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____5904 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____5915 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____5926 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____5937 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____5949 -> false
  
let (__proj__Reflectable__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Reflectable _0 -> _0 
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discriminator _0 -> true | uu____5968 -> false
  
let (__proj__Discriminator__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Discriminator _0 -> _0 
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____5991 -> false
  
let (__proj__Projector__item___0 :
  qualifier -> (FStar_Ident.lident * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | RecordType _0 -> true | uu____6030 -> false
  
let (__proj__RecordType__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee  -> match projectee with | RecordType _0 -> _0 
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | RecordConstructor _0 -> true | uu____6081 -> false
  
let (__proj__RecordConstructor__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee  -> match projectee with | RecordConstructor _0 -> _0 
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Action _0 -> true | uu____6124 -> false
  
let (__proj__Action__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Action _0 -> _0 
let (uu___is_ExceptionConstructor : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ExceptionConstructor  -> true
    | uu____6142 -> false
  
let (uu___is_HasMaskedEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | HasMaskedEffect  -> true | uu____6153 -> false
  
let (uu___is_Effect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect  -> true | uu____6164 -> false
  
let (uu___is_OnlyName : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | OnlyName  -> true | uu____6175 -> false
  
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
  
type eff_decl =
  {
  cattributes: cflag Prims.list ;
  mname: FStar_Ident.lident ;
  univs: univ_names ;
  binders: binders ;
  signature: tscheme ;
  ret_wp: tscheme ;
  bind_wp: tscheme ;
  if_then_else: tscheme ;
  ite_wp: tscheme ;
  stronger: tscheme ;
  close_wp: tscheme ;
  trivial: tscheme ;
  repr: tscheme ;
  return_repr: tscheme ;
  bind_repr: tscheme ;
  actions: action Prims.list ;
  eff_attrs: attribute Prims.list }
let (__proj__Mkeff_decl__item__cattributes : eff_decl -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> cattributes
  
let (__proj__Mkeff_decl__item__mname : eff_decl -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> mname
  
let (__proj__Mkeff_decl__item__univs : eff_decl -> univ_names) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> univs
  
let (__proj__Mkeff_decl__item__binders : eff_decl -> binders) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> binders
  
let (__proj__Mkeff_decl__item__signature : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> signature
  
let (__proj__Mkeff_decl__item__ret_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> ret_wp
  
let (__proj__Mkeff_decl__item__bind_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> bind_wp
  
let (__proj__Mkeff_decl__item__if_then_else : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> if_then_else
  
let (__proj__Mkeff_decl__item__ite_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> ite_wp
  
let (__proj__Mkeff_decl__item__stronger : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> stronger
  
let (__proj__Mkeff_decl__item__close_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> close_wp
  
let (__proj__Mkeff_decl__item__trivial : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> trivial
  
let (__proj__Mkeff_decl__item__repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> repr
  
let (__proj__Mkeff_decl__item__return_repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> return_repr
  
let (__proj__Mkeff_decl__item__bind_repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> bind_repr
  
let (__proj__Mkeff_decl__item__actions : eff_decl -> action Prims.list) =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> actions
  
let (__proj__Mkeff_decl__item__eff_attrs : eff_decl -> attribute Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { cattributes; mname; univs; binders; signature; ret_wp; bind_wp;
        if_then_else; ite_wp; stronger; close_wp; trivial; repr; return_repr;
        bind_repr; actions; eff_attrs;_} -> eff_attrs
  
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
  sigattrs: attribute Prims.list }
let (uu___is_Sig_inductive_typ : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_inductive_typ _0 -> true | uu____7252 -> false
  
let (__proj__Sig_inductive_typ__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident
      Prims.list * FStar_Ident.lident Prims.list))
  = fun projectee  -> match projectee with | Sig_inductive_typ _0 -> _0 
let (uu___is_Sig_bundle : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_bundle _0 -> true | uu____7327 -> false
  
let (__proj__Sig_bundle__item___0 :
  sigelt' -> (sigelt Prims.list * FStar_Ident.lident Prims.list)) =
  fun projectee  -> match projectee with | Sig_bundle _0 -> _0 
let (uu___is_Sig_datacon : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_datacon _0 -> true | uu____7385 -> false
  
let (__proj__Sig_datacon__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int *
      FStar_Ident.lident Prims.list))
  = fun projectee  -> match projectee with | Sig_datacon _0 -> _0 
let (uu___is_Sig_declare_typ : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_declare_typ _0 -> true | uu____7455 -> false
  
let (__proj__Sig_declare_typ__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * typ)) =
  fun projectee  -> match projectee with | Sig_declare_typ _0 -> _0 
let (uu___is_Sig_let : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_let _0 -> true | uu____7498 -> false
  
let (__proj__Sig_let__item___0 :
  sigelt' -> (letbindings * FStar_Ident.lident Prims.list)) =
  fun projectee  -> match projectee with | Sig_let _0 -> _0 
let (uu___is_Sig_main : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_main _0 -> true | uu____7535 -> false
  
let (__proj__Sig_main__item___0 : sigelt' -> term) =
  fun projectee  -> match projectee with | Sig_main _0 -> _0 
let (uu___is_Sig_assume : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_assume _0 -> true | uu____7560 -> false
  
let (__proj__Sig_assume__item___0 :
  sigelt' -> (FStar_Ident.lident * univ_names * formula)) =
  fun projectee  -> match projectee with | Sig_assume _0 -> _0 
let (uu___is_Sig_new_effect : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_new_effect _0 -> true | uu____7597 -> false
  
let (__proj__Sig_new_effect__item___0 : sigelt' -> eff_decl) =
  fun projectee  -> match projectee with | Sig_new_effect _0 -> _0 
let (uu___is_Sig_new_effect_for_free : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Sig_new_effect_for_free _0 -> true
    | uu____7616 -> false
  
let (__proj__Sig_new_effect_for_free__item___0 : sigelt' -> eff_decl) =
  fun projectee  -> match projectee with | Sig_new_effect_for_free _0 -> _0 
let (uu___is_Sig_sub_effect : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_sub_effect _0 -> true | uu____7635 -> false
  
let (__proj__Sig_sub_effect__item___0 : sigelt' -> sub_eff) =
  fun projectee  -> match projectee with | Sig_sub_effect _0 -> _0 
let (uu___is_Sig_effect_abbrev : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_effect_abbrev _0 -> true | uu____7666 -> false
  
let (__proj__Sig_effect_abbrev__item___0 :
  sigelt' ->
    (FStar_Ident.lident * univ_names * binders * comp * cflag Prims.list))
  = fun projectee  -> match projectee with | Sig_effect_abbrev _0 -> _0 
let (uu___is_Sig_pragma : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_pragma _0 -> true | uu____7721 -> false
  
let (__proj__Sig_pragma__item___0 : sigelt' -> pragma) =
  fun projectee  -> match projectee with | Sig_pragma _0 -> _0 
let (uu___is_Sig_splice : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_splice _0 -> true | uu____7746 -> false
  
let (__proj__Sig_splice__item___0 :
  sigelt' -> (FStar_Ident.lident Prims.list * term)) =
  fun projectee  -> match projectee with | Sig_splice _0 -> _0 
let (__proj__Mksigelt__item__sigel : sigelt -> sigelt') =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs;_} -> sigel
  
let (__proj__Mksigelt__item__sigrng : sigelt -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs;_} -> sigrng
  
let (__proj__Mksigelt__item__sigquals : sigelt -> qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs;_} -> sigquals
  
let (__proj__Mksigelt__item__sigmeta : sigelt -> sig_metadata) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs;_} -> sigmeta
  
let (__proj__Mksigelt__item__sigattrs : sigelt -> attribute Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigel; sigrng; sigquals; sigmeta; sigattrs;_} -> sigattrs
  
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
      (fun uu___0_7968  ->
         match uu___0_7968 with
         | Reflectable uu____7970 -> true
         | uu____7972 -> false) l
  
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
      let uu___413_8090 = x  in
      let uu____8091 =
        FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____8091;
        index = (uu___413_8090.index);
        sort = (uu___413_8090.sort)
      }
  
let (on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo) =
  fun f  ->
    fun qi  ->
      let aq =
        FStar_List.map
          (fun uu____8128  ->
             match uu____8128 with
             | (bv,t) -> let uu____8139 = f t  in (bv, uu____8139))
          qi.antiquotes
         in
      let uu___421_8140 = qi  in
      { qkind = (uu___421_8140.qkind); antiquotes = aq }
  
let (lookup_aq : bv -> antiquotations -> term FStar_Pervasives_Native.option)
  =
  fun bv  ->
    fun aq  ->
      let uu____8156 =
        FStar_List.tryFind
          (fun uu____8174  ->
             match uu____8174 with | (bv',uu____8183) -> bv_eq bv bv') aq
         in
      match uu____8156 with
      | FStar_Pervasives_Native.Some (uu____8190,e) ->
          FStar_Pervasives_Native.Some e
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let syn :
  'Auu____8221 'Auu____8222 'Auu____8223 .
    'Auu____8221 ->
      'Auu____8222 ->
        ('Auu____8222 -> 'Auu____8221 -> 'Auu____8223) -> 'Auu____8223
  = fun p  -> fun k  -> fun f  -> f k p 
let mk_fvs :
  'Auu____8254 .
    unit -> 'Auu____8254 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8263  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let mk_uvs :
  'Auu____8271 .
    unit -> 'Auu____8271 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____8280  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (new_bv_set : unit -> bv FStar_Util.set) =
  fun uu____8290  -> FStar_Util.new_set order_bv 
let (new_id_set : unit -> FStar_Ident.ident FStar_Util.set) =
  fun uu____8300  -> FStar_Util.new_set order_ident 
let (new_fv_set : unit -> FStar_Ident.lident FStar_Util.set) =
  fun uu____8310  -> FStar_Util.new_set order_fv 
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x  ->
    fun y  ->
      let uu____8325 = FStar_Ident.text_of_id x  in
      let uu____8327 = FStar_Ident.text_of_id y  in
      FStar_String.compare uu____8325 uu____8327
  
let (new_universe_names_set : unit -> univ_name FStar_Util.set) =
  fun uu____8336  -> FStar_Util.new_set order_univ_name 
let (eq_binding : binding -> binding -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with
      | (Binding_var bv1,Binding_var bv2) -> bv_eq bv1 bv2
      | (Binding_lid (lid1,uu____8355),Binding_lid (lid2,uu____8357)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1,Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu____8392 -> false
  
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
    fun uu____8446  ->
      fun r  ->
        let uu____8450 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        { n = t; pos = r; vars = uu____8450 }
  
let (bv_to_tm : bv -> term) =
  fun bv  ->
    let uu____8461 = range_of_bv bv  in
    mk (Tm_bvar bv) FStar_Pervasives_Native.None uu____8461
  
let (bv_to_name : bv -> term) =
  fun bv  ->
    let uu____8468 = range_of_bv bv  in
    mk (Tm_name bv) FStar_Pervasives_Native.None uu____8468
  
let (binders_to_names : binders -> term Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.map
         (fun uu____8498  ->
            match uu____8498 with | (x,uu____8506) -> bv_to_name x))
  
let (mk_Tm_app : term -> args -> mk_t) =
  fun t1  ->
    fun args  ->
      fun k  ->
        fun p  ->
          match args with
          | [] -> t1
          | uu____8536 ->
              mk (Tm_app (t1, args)) FStar_Pervasives_Native.None p
  
let (mk_Tm_uinst : term -> universes -> term) =
  fun t  ->
    fun uu___1_8561  ->
      match uu___1_8561 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____8563 ->
               mk (Tm_uinst (t, us)) FStar_Pervasives_Native.None t.pos
           | uu____8566 -> failwith "Unexpected universe instantiation")
  
let (extend_app_n : term -> args -> mk_t) =
  fun t  ->
    fun args'  ->
      fun kopt  ->
        fun r  ->
          match t.n with
          | Tm_app (head1,args) ->
              mk_Tm_app head1 (FStar_List.append args args') kopt r
          | uu____8625 -> mk_Tm_app t args' kopt r
  
let (extend_app : term -> arg -> mk_t) =
  fun t  -> fun arg  -> fun kopt  -> fun r  -> extend_app_n t [arg] kopt r 
let (mk_Tm_delayed : (term * subst_ts) -> FStar_Range.range -> term) =
  fun lr  ->
    fun pos  ->
      let uu____8682 =
        let uu____8689 =
          let uu____8690 =
            let uu____8713 = FStar_Util.mk_ref FStar_Pervasives_Native.None
               in
            (lr, uu____8713)  in
          Tm_delayed uu____8690  in
        mk uu____8689  in
      uu____8682 FStar_Pervasives_Native.None pos
  
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
  fun uu____8821  ->
    match uu____8821 with
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
      sigattrs = []
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
    | uu____8906 -> false
  
let (is_type : term -> Prims.bool) =
  fun t  -> match t.n with | Tm_type uu____8916 -> true | uu____8918 -> false 
let (null_id : FStar_Ident.ident) =
  FStar_Ident.mk_ident ("_", FStar_Range.dummyRange) 
let (null_bv : term -> bv) =
  fun k  -> { ppname = null_id; index = Prims.int_zero; sort = k } 
let (mk_binder : bv -> binder) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (null_binder : term -> binder) =
  fun t  ->
    let uu____8944 = null_bv t  in (uu____8944, FStar_Pervasives_Native.None)
  
let (imp_tag : arg_qualifier) = Implicit false 
let (iarg : term -> arg) =
  fun t  -> (t, (FStar_Pervasives_Native.Some imp_tag)) 
let (as_arg : term -> arg) = fun t  -> (t, FStar_Pervasives_Native.None) 
let (is_null_bv : bv -> Prims.bool) =
  fun b  -> (b.ppname).FStar_Ident.idText = null_id.FStar_Ident.idText 
let (is_null_binder : binder -> Prims.bool) =
  fun b  -> is_null_bv (FStar_Pervasives_Native.fst b) 
let (is_top_level : letbinding Prims.list -> Prims.bool) =
  fun uu___2_8994  ->
    match uu___2_8994 with
    | { lbname = FStar_Util.Inr uu____8998; lbunivs = uu____8999;
        lbtyp = uu____9000; lbeff = uu____9001; lbdef = uu____9002;
        lbattrs = uu____9003; lbpos = uu____9004;_}::uu____9005 -> true
    | uu____9019 -> false
  
let (freenames_of_binders : binders -> freenames) =
  fun bs  ->
    FStar_List.fold_right
      (fun uu____9041  ->
         fun out  ->
           match uu____9041 with | (x,uu____9054) -> FStar_Util.set_add x out)
      bs no_names
  
let (binders_of_list : bv Prims.list -> binders) =
  fun fvs  ->
    FStar_All.pipe_right fvs
      (FStar_List.map (fun t  -> (t, FStar_Pervasives_Native.None)))
  
let (binders_of_freenames : freenames -> binders) =
  fun fvs  ->
    let uu____9087 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____9087 binders_of_list
  
let (is_implicit : aqual -> Prims.bool) =
  fun uu___3_9098  ->
    match uu___3_9098 with
    | FStar_Pervasives_Native.Some (Implicit uu____9100) -> true
    | uu____9103 -> false
  
let (as_implicit : Prims.bool -> aqual) =
  fun uu___4_9111  ->
    if uu___4_9111
    then FStar_Pervasives_Native.Some imp_tag
    else FStar_Pervasives_Native.None
  
let (pat_bvs : pat -> bv Prims.list) =
  fun p  ->
    let rec aux b p1 =
      match p1.v with
      | Pat_dot_term uu____9149 -> b
      | Pat_constant uu____9156 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____9159,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____9193  ->
                 match uu____9193 with | (p2,uu____9206) -> aux b1 p2) b pats
       in
    let uu____9213 = aux [] p  in
    FStar_All.pipe_left FStar_List.rev uu____9213
  
let (range_of_ropt :
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Range.range) =
  fun uu___5_9227  ->
    match uu___5_9227 with
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
        let uu____9267 = FStar_Ident.next_id ()  in
        { ppname = id1; index = uu____9267; sort = t }
  
let (new_bv : FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv)
  = fun ropt  -> fun t  -> gen_bv FStar_Ident.reserved_prefix ropt t 
let (freshen_bv : bv -> bv) =
  fun bv  ->
    let uu____9290 = is_null_bv bv  in
    if uu____9290
    then
      let uu____9293 =
        let uu____9296 = range_of_bv bv  in
        FStar_Pervasives_Native.Some uu____9296  in
      new_bv uu____9293 bv.sort
    else
      (let uu___602_9299 = bv  in
       let uu____9300 = FStar_Ident.next_id ()  in
       {
         ppname = (uu___602_9299.ppname);
         index = uu____9300;
         sort = (uu___602_9299.sort)
       })
  
let (freshen_binder : binder -> binder) =
  fun b  ->
    let uu____9308 = b  in
    match uu____9308 with
    | (bv,aq) -> let uu____9315 = freshen_bv bv  in (uu____9315, aq)
  
let (new_univ_name :
  FStar_Range.range FStar_Pervasives_Native.option -> univ_name) =
  fun ropt  ->
    let id1 = FStar_Ident.next_id ()  in
    let uu____9330 =
      let uu____9336 =
        let uu____9338 = FStar_Util.string_of_int id1  in
        Prims.op_Hat FStar_Ident.reserved_prefix uu____9338  in
      (uu____9336, (range_of_ropt ropt))  in
    FStar_Ident.mk_ident uu____9330
  
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
      | uu____9420 -> false
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun fv1  ->
    fun fv2  -> FStar_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
  
let (fv_eq_lid : fv -> FStar_Ident.lident -> Prims.bool) =
  fun fv  -> fun lid  -> FStar_Ident.lid_equals (fv.fv_name).v lid 
let (set_bv_range : bv -> FStar_Range.range -> bv) =
  fun bv  ->
    fun r  ->
      let uu___632_9469 = bv  in
      let uu____9470 =
        FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____9470;
        index = (uu___632_9469.index);
        sort = (uu___632_9469.sort)
      }
  
let (lid_as_fv :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> fv)
  =
  fun l  ->
    fun dd  ->
      fun dq  ->
        let uu____9492 =
          let uu____9493 = FStar_Ident.range_of_lid l  in
          withinfo l uu____9493  in
        { fv_name = uu____9492; fv_delta = dd; fv_qual = dq }
  
let (fv_to_tm : fv -> term) =
  fun fv  ->
    let uu____9500 = FStar_Ident.range_of_lid (fv.fv_name).v  in
    mk (Tm_fvar fv) FStar_Pervasives_Native.None uu____9500
  
let (fvar :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> term)
  =
  fun l  ->
    fun dd  ->
      fun dq  -> let uu____9521 = lid_as_fv l dd dq  in fv_to_tm uu____9521
  
let (lid_of_fv : fv -> FStar_Ident.lid) = fun fv  -> (fv.fv_name).v 
let (range_of_fv : fv -> FStar_Range.range) =
  fun fv  ->
    let uu____9534 = lid_of_fv fv  in FStar_Ident.range_of_lid uu____9534
  
let (set_range_of_fv : fv -> FStar_Range.range -> fv) =
  fun fv  ->
    fun r  ->
      let uu___645_9546 = fv  in
      let uu____9547 =
        let uu___647_9548 = fv.fv_name  in
        let uu____9549 =
          let uu____9550 = lid_of_fv fv  in
          FStar_Ident.set_lid_range uu____9550 r  in
        { v = uu____9549; p = (uu___647_9548.p) }  in
      {
        fv_name = uu____9547;
        fv_delta = (uu___645_9546.fv_delta);
        fv_qual = (uu___645_9546.fv_qual)
      }
  
let (has_simple_attribute : term Prims.list -> Prims.string -> Prims.bool) =
  fun l  ->
    fun s  ->
      FStar_List.existsb
        (fun uu___6_9576  ->
           match uu___6_9576 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____9581));
               pos = uu____9582; vars = uu____9583;_} when data = s -> true
           | uu____9590 -> false) l
  
let rec (eq_pat : pat -> pat -> Prims.bool) =
  fun p1  ->
    fun p2  ->
      match ((p1.v), (p2.v)) with
      | (Pat_constant c1,Pat_constant c2) -> FStar_Const.eq_const c1 c2
      | (Pat_cons (fv1,as1),Pat_cons (fv2,as2)) ->
          let uu____9649 = fv_eq fv1 fv2  in
          if uu____9649
          then
            let uu____9654 = FStar_List.zip as1 as2  in
            FStar_All.pipe_right uu____9654
              (FStar_List.for_all
                 (fun uu____9721  ->
                    match uu____9721 with
                    | ((p11,b1),(p21,b2)) -> (b1 = b2) && (eq_pat p11 p21)))
          else false
      | (Pat_var uu____9759,Pat_var uu____9760) -> true
      | (Pat_wild uu____9762,Pat_wild uu____9763) -> true
      | (Pat_dot_term (bv1,t1),Pat_dot_term (bv2,t2)) -> true
      | (uu____9778,uu____9779) -> false
  
let (delta_constant : delta_depth) = Delta_constant_at_level Prims.int_zero 
let (delta_equational : delta_depth) =
  Delta_equational_at_level Prims.int_zero 
let (fvconst : FStar_Ident.lident -> fv) =
  fun l  -> lid_as_fv l delta_constant FStar_Pervasives_Native.None 
let (tconst : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9797 =
      let uu____9804 = let uu____9805 = fvconst l  in Tm_fvar uu____9805  in
      mk uu____9804  in
    uu____9797 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tabbrev : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9812 =
      let uu____9819 =
        let uu____9820 =
          lid_as_fv l (Delta_constant_at_level Prims.int_one)
            FStar_Pervasives_Native.None
           in
        Tm_fvar uu____9820  in
      mk uu____9819  in
    uu____9812 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tdataconstr : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____9828 =
      lid_as_fv l delta_constant (FStar_Pervasives_Native.Some Data_ctor)  in
    fv_to_tm uu____9828
  
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
let (t_tactic_unit : term) =
  let uu____9848 =
    let uu____9853 =
      let uu____9854 = tabbrev FStar_Parser_Const.tactic_lid  in
      mk_Tm_uinst uu____9854 [U_zero]  in
    let uu____9855 = let uu____9856 = as_arg t_unit  in [uu____9856]  in
    mk_Tm_app uu____9853 uu____9855  in
  uu____9848 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (t_list_of : term -> term) =
  fun t  ->
    let uu____9887 =
      let uu____9892 =
        let uu____9893 = tabbrev FStar_Parser_Const.list_lid  in
        mk_Tm_uinst uu____9893 [U_zero]  in
      let uu____9894 = let uu____9895 = as_arg t  in [uu____9895]  in
      mk_Tm_app uu____9892 uu____9894  in
    uu____9887 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_option_of : term -> term) =
  fun t  ->
    let uu____9926 =
      let uu____9931 =
        let uu____9932 = tabbrev FStar_Parser_Const.option_lid  in
        mk_Tm_uinst uu____9932 [U_zero]  in
      let uu____9933 = let uu____9934 = as_arg t  in [uu____9934]  in
      mk_Tm_app uu____9931 uu____9933  in
    uu____9926 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_tuple2_of : term -> term -> term) =
  fun t1  ->
    fun t2  ->
      let uu____9970 =
        let uu____9975 =
          let uu____9976 = tabbrev FStar_Parser_Const.lid_tuple2  in
          mk_Tm_uinst uu____9976 [U_zero; U_zero]  in
        let uu____9977 =
          let uu____9978 = as_arg t1  in
          let uu____9987 = let uu____9998 = as_arg t2  in [uu____9998]  in
          uu____9978 :: uu____9987  in
        mk_Tm_app uu____9975 uu____9977  in
      uu____9970 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_either_of : term -> term -> term) =
  fun t1  ->
    fun t2  ->
      let uu____10042 =
        let uu____10047 =
          let uu____10048 = tabbrev FStar_Parser_Const.either_lid  in
          mk_Tm_uinst uu____10048 [U_zero; U_zero]  in
        let uu____10049 =
          let uu____10050 = as_arg t1  in
          let uu____10059 = let uu____10070 = as_arg t2  in [uu____10070]  in
          uu____10050 :: uu____10059  in
        mk_Tm_app uu____10047 uu____10049  in
      uu____10042 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (unit_const : term) =
  mk (Tm_constant FStar_Const.Const_unit) FStar_Pervasives_Native.None
    FStar_Range.dummyRange
  