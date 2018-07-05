open Prims
type 'a withinfo_t = {
  v: 'a ;
  p: FStar_Range.range }[@@deriving yojson,show]
let __proj__Mkwithinfo_t__item__v : 'a . 'a withinfo_t -> 'a =
  fun projectee  ->
    match projectee with | { v = __fname__v; p = __fname__p;_} -> __fname__v
  
let __proj__Mkwithinfo_t__item__p : 'a . 'a withinfo_t -> FStar_Range.range =
  fun projectee  ->
    match projectee with | { v = __fname__v; p = __fname__p;_} -> __fname__p
  
type var = FStar_Ident.lident withinfo_t[@@deriving yojson,show]
type sconst = FStar_Const.sconst[@@deriving yojson,show]
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | LightOff [@@deriving yojson,show]
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____74 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____90 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____112 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____131 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____137 -> false
  
type 'a memo =
  (('a FStar_Pervasives_Native.option FStar_ST.ref)[@printer
                                                     fun fmt  ->
                                                       fun _  ->
                                                         Format.pp_print_string
                                                           fmt "None"])
[@@deriving yojson,show]
type emb_typ =
  | ET_abstract 
  | ET_fun of (emb_typ,emb_typ) FStar_Pervasives_Native.tuple2 
  | ET_app of (Prims.string,emb_typ Prims.list)
  FStar_Pervasives_Native.tuple2 
let (uu___is_ET_abstract : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_abstract  -> true | uu____171 -> false
  
let (uu___is_ET_fun : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_fun _0 -> true | uu____182 -> false
  
let (__proj__ET_fun__item___0 :
  emb_typ -> (emb_typ,emb_typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ET_fun _0 -> _0 
let (uu___is_ET_app : emb_typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | ET_app _0 -> true | uu____214 -> false
  
let (__proj__ET_app__item___0 :
  emb_typ -> (Prims.string,emb_typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | ET_app _0 -> _0 
type version = {
  major: Prims.int ;
  minor: Prims.int }[@@deriving yojson,show]
let (__proj__Mkversion__item__major : version -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { major = __fname__major; minor = __fname__minor;_} -> __fname__major
  
let (__proj__Mkversion__item__minor : version -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { major = __fname__major; minor = __fname__minor;_} -> __fname__minor
  
type universe =
  | U_zero 
  | U_succ of universe 
  | U_max of universe Prims.list 
  | U_bvar of Prims.int 
  | U_name of FStar_Ident.ident 
  | U_unif of
  (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,version)
  FStar_Pervasives_Native.tuple2 
  | U_unknown [@@deriving yojson,show]
let (uu___is_U_zero : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_zero  -> true | uu____304 -> false
  
let (uu___is_U_succ : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_succ _0 -> true | uu____311 -> false
  
let (__proj__U_succ__item___0 : universe -> universe) =
  fun projectee  -> match projectee with | U_succ _0 -> _0 
let (uu___is_U_max : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_max _0 -> true | uu____327 -> false
  
let (__proj__U_max__item___0 : universe -> universe Prims.list) =
  fun projectee  -> match projectee with | U_max _0 -> _0 
let (uu___is_U_bvar : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_bvar _0 -> true | uu____347 -> false
  
let (__proj__U_bvar__item___0 : universe -> Prims.int) =
  fun projectee  -> match projectee with | U_bvar _0 -> _0 
let (uu___is_U_name : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_name _0 -> true | uu____361 -> false
  
let (__proj__U_name__item___0 : universe -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | U_name _0 -> _0 
let (uu___is_U_unif : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_unif _0 -> true | uu____383 -> false
  
let (__proj__U_unif__item___0 :
  universe ->
    (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,version)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | U_unif _0 -> _0 
let (uu___is_U_unknown : universe -> Prims.bool) =
  fun projectee  ->
    match projectee with | U_unknown  -> true | uu____420 -> false
  
type univ_name = FStar_Ident.ident[@@deriving yojson,show]
type universe_uvar =
  (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,version)
    FStar_Pervasives_Native.tuple2[@@deriving yojson,show]
type univ_names = univ_name Prims.list[@@deriving yojson,show]
type universes = universe Prims.list[@@deriving yojson,show]
type monad_name = FStar_Ident.lident[@@deriving yojson,show]
type quote_kind =
  | Quote_static 
  | Quote_dynamic [@@deriving yojson,show]
let (uu___is_Quote_static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote_static  -> true | uu____438 -> false
  
let (uu___is_Quote_dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote_dynamic  -> true | uu____444 -> false
  
type maybe_set_use_range =
  | NoUseRange 
  | SomeUseRange of FStar_Range.range [@@deriving yojson,show]
let (uu___is_NoUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUseRange  -> true | uu____455 -> false
  
let (uu___is_SomeUseRange : maybe_set_use_range -> Prims.bool) =
  fun projectee  ->
    match projectee with | SomeUseRange _0 -> true | uu____462 -> false
  
let (__proj__SomeUseRange__item___0 :
  maybe_set_use_range -> FStar_Range.range) =
  fun projectee  -> match projectee with | SomeUseRange _0 -> _0 
type delta_depth =
  | Delta_constant_at_level of Prims.int 
  | Delta_equational_at_level of Prims.int 
  | Delta_abstract of delta_depth [@@deriving yojson,show]
let (uu___is_Delta_constant_at_level : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Delta_constant_at_level _0 -> true
    | uu____491 -> false
  
let (__proj__Delta_constant_at_level__item___0 : delta_depth -> Prims.int) =
  fun projectee  -> match projectee with | Delta_constant_at_level _0 -> _0 
let (uu___is_Delta_equational_at_level : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Delta_equational_at_level _0 -> true
    | uu____505 -> false
  
let (__proj__Delta_equational_at_level__item___0 : delta_depth -> Prims.int)
  =
  fun projectee  -> match projectee with | Delta_equational_at_level _0 -> _0 
let (uu___is_Delta_abstract : delta_depth -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta_abstract _0 -> true | uu____519 -> false
  
let (__proj__Delta_abstract__item___0 : delta_depth -> delta_depth) =
  fun projectee  -> match projectee with | Delta_abstract _0 -> _0 
type should_check_uvar =
  | Allow_unresolved 
  | Allow_untyped 
  | Strict [@@deriving yojson,show]
let (uu___is_Allow_unresolved : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Allow_unresolved  -> true | uu____532 -> false
  
let (uu___is_Allow_untyped : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Allow_untyped  -> true | uu____538 -> false
  
let (uu___is_Strict : should_check_uvar -> Prims.bool) =
  fun projectee  ->
    match projectee with | Strict  -> true | uu____544 -> false
  
type term' =
  | Tm_bvar of bv 
  | Tm_name of bv 
  | Tm_fvar of fv 
  | Tm_uinst of (term' syntax,universes) FStar_Pervasives_Native.tuple2 
  | Tm_constant of sconst 
  | Tm_type of universe 
  | Tm_abs of
  ((bv,arg_qualifier FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2 Prims.list,term' syntax,residual_comp
                                                              FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3 
  | Tm_arrow of
  ((bv,arg_qualifier FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2 Prims.list,comp' syntax)
  FStar_Pervasives_Native.tuple2 
  | Tm_refine of (bv,term' syntax) FStar_Pervasives_Native.tuple2 
  | Tm_app of
  (term' syntax,(term' syntax,arg_qualifier FStar_Pervasives_Native.option)
                  FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Tm_match of
  (term' syntax,(pat' withinfo_t,term' syntax FStar_Pervasives_Native.option,
                  term' syntax) FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Tm_ascribed of
  (term' syntax,((term' syntax,comp' syntax) FStar_Util.either,term' syntax
                                                                 FStar_Pervasives_Native.option)
                  FStar_Pervasives_Native.tuple2,FStar_Ident.lident
                                                   FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3 
  | Tm_let of
  ((Prims.bool,letbinding Prims.list) FStar_Pervasives_Native.tuple2,
  term' syntax) FStar_Pervasives_Native.tuple2 
  | Tm_uvar of
  (ctx_uvar,(subst_elt Prims.list Prims.list,maybe_set_use_range)
              FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
  | Tm_delayed of
  ((term' syntax,(subst_elt Prims.list Prims.list,maybe_set_use_range)
                   FStar_Pervasives_Native.tuple2)
     FStar_Pervasives_Native.tuple2,term' syntax memo)
  FStar_Pervasives_Native.tuple2 
  | Tm_meta of (term' syntax,metadata) FStar_Pervasives_Native.tuple2 
  | Tm_lazy of lazyinfo 
  | Tm_quoted of (term' syntax,quoteinfo) FStar_Pervasives_Native.tuple2 
  | Tm_unknown 
and ctx_uvar =
  {
  ctx_uvar_head:
    (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,
      version) FStar_Pervasives_Native.tuple2
    ;
  ctx_uvar_gamma: binding Prims.list ;
  ctx_uvar_binders:
    (bv,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  ctx_uvar_typ: term' syntax ;
  ctx_uvar_reason: Prims.string ;
  ctx_uvar_should_check: should_check_uvar ;
  ctx_uvar_range: FStar_Range.range }
and pat' =
  | Pat_constant of sconst 
  | Pat_cons of
  (fv,(pat' withinfo_t,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Pat_var of bv 
  | Pat_wild of bv 
  | Pat_dot_term of (bv,term' syntax) FStar_Pervasives_Native.tuple2 
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
  antiquotes: (bv,term' syntax) FStar_Pervasives_Native.tuple2 Prims.list }
and comp_typ =
  {
  comp_univs: universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: term' syntax ;
  effect_args:
    (term' syntax,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  flags: cflags Prims.list }
and comp' =
  | Total of (term' syntax,universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | GTotal of (term' syntax,universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Comp of comp_typ 
and cflags =
  | TOTAL 
  | MLEFFECT 
  | RETURN 
  | PARTIAL_RETURN 
  | SOMETRIVIAL 
  | TRIVIAL_POSTCONDITION 
  | SHOULD_NOT_INLINE 
  | LEMMA 
  | CPS 
  | DECREASES of term' syntax 
and metadata =
  | Meta_pattern of
  (term' syntax,arg_qualifier FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 Prims.list Prims.list 
  | Meta_named of FStar_Ident.lident 
  | Meta_labeled of (Prims.string,FStar_Range.range,Prims.bool)
  FStar_Pervasives_Native.tuple3 
  | Meta_desugared of meta_source_info 
  | Meta_monadic of (monad_name,term' syntax) FStar_Pervasives_Native.tuple2
  
  | Meta_monadic_lift of (monad_name,monad_name,term' syntax)
  FStar_Pervasives_Native.tuple3 
and meta_source_info =
  | Sequence 
  | Primop 
  | Masked_effect 
  | Meta_smt_pat 
  | Mutable_alloc 
  | Mutable_rval 
and fv_qual =
  | Data_ctor 
  | Record_projector of (FStar_Ident.lident,FStar_Ident.ident)
  FStar_Pervasives_Native.tuple2 
  | Record_ctor of (FStar_Ident.lident,FStar_Ident.ident Prims.list)
  FStar_Pervasives_Native.tuple2 
and subst_elt =
  | DB of (Prims.int,bv) FStar_Pervasives_Native.tuple2 
  | NM of (bv,Prims.int) FStar_Pervasives_Native.tuple2 
  | NT of (bv,term' syntax) FStar_Pervasives_Native.tuple2 
  | UN of (Prims.int,universe) FStar_Pervasives_Native.tuple2 
  | UD of (univ_name,Prims.int) FStar_Pervasives_Native.tuple2 
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
  residual_flags: cflags Prims.list }
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
  | Lazy_sigelt 
  | Lazy_uvar 
  | Lazy_embedding of (emb_typ,term' syntax FStar_Common.thunk)
  FStar_Pervasives_Native.tuple2 
and binding =
  | Binding_var of bv 
  | Binding_lid of
  (FStar_Ident.lident,(univ_name Prims.list,term' syntax)
                        FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
  | Binding_univ of univ_name 
and arg_qualifier =
  | Implicit of Prims.bool 
  | Meta of term' syntax 
  | Equality 
let (uu___is_Tm_bvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_bvar _0 -> true | uu____1408 -> false
  
let (__proj__Tm_bvar__item___0 : term' -> bv) =
  fun projectee  -> match projectee with | Tm_bvar _0 -> _0 
let (uu___is_Tm_name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_name _0 -> true | uu____1422 -> false
  
let (__proj__Tm_name__item___0 : term' -> bv) =
  fun projectee  -> match projectee with | Tm_name _0 -> _0 
let (uu___is_Tm_fvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_fvar _0 -> true | uu____1436 -> false
  
let (__proj__Tm_fvar__item___0 : term' -> fv) =
  fun projectee  -> match projectee with | Tm_fvar _0 -> _0 
let (uu___is_Tm_uinst : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_uinst _0 -> true | uu____1456 -> false
  
let (__proj__Tm_uinst__item___0 :
  term' -> (term' syntax,universes) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Tm_uinst _0 -> _0 
let (uu___is_Tm_constant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_constant _0 -> true | uu____1488 -> false
  
let (__proj__Tm_constant__item___0 : term' -> sconst) =
  fun projectee  -> match projectee with | Tm_constant _0 -> _0 
let (uu___is_Tm_type : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_type _0 -> true | uu____1502 -> false
  
let (__proj__Tm_type__item___0 : term' -> universe) =
  fun projectee  -> match projectee with | Tm_type _0 -> _0 
let (uu___is_Tm_abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_abs _0 -> true | uu____1534 -> false
  
let (__proj__Tm_abs__item___0 :
  term' ->
    ((bv,arg_qualifier FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,term' syntax,residual_comp
                                                                FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Tm_abs _0 -> _0 
let (uu___is_Tm_arrow : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_arrow _0 -> true | uu____1616 -> false
  
let (__proj__Tm_arrow__item___0 :
  term' ->
    ((bv,arg_qualifier FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,comp' syntax)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tm_arrow _0 -> _0 
let (uu___is_Tm_refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_refine _0 -> true | uu____1678 -> false
  
let (__proj__Tm_refine__item___0 :
  term' -> (bv,term' syntax) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Tm_refine _0 -> _0 
let (uu___is_Tm_app : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_app _0 -> true | uu____1726 -> false
  
let (__proj__Tm_app__item___0 :
  term' ->
    (term' syntax,(term' syntax,arg_qualifier FStar_Pervasives_Native.option)
                    FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tm_app _0 -> _0 
let (uu___is_Tm_match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_match _0 -> true | uu____1810 -> false
  
let (__proj__Tm_match__item___0 :
  term' ->
    (term' syntax,(pat' withinfo_t,term' syntax
                                     FStar_Pervasives_Native.option,term'
                                                                    syntax)
                    FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tm_match _0 -> _0 
let (uu___is_Tm_ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_ascribed _0 -> true | uu____1916 -> false
  
let (__proj__Tm_ascribed__item___0 :
  term' ->
    (term' syntax,((term' syntax,comp' syntax) FStar_Util.either,term' syntax
                                                                   FStar_Pervasives_Native.option)
                    FStar_Pervasives_Native.tuple2,FStar_Ident.lident
                                                     FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Tm_ascribed _0 -> _0 
let (uu___is_Tm_let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_let _0 -> true | uu____2020 -> false
  
let (__proj__Tm_let__item___0 :
  term' ->
    ((Prims.bool,letbinding Prims.list) FStar_Pervasives_Native.tuple2,
      term' syntax) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tm_let _0 -> _0 
let (uu___is_Tm_uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_uvar _0 -> true | uu____2082 -> false
  
let (__proj__Tm_uvar__item___0 :
  term' ->
    (ctx_uvar,(subst_elt Prims.list Prims.list,maybe_set_use_range)
                FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tm_uvar _0 -> _0 
let (uu___is_Tm_delayed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_delayed _0 -> true | uu____2154 -> false
  
let (__proj__Tm_delayed__item___0 :
  term' ->
    ((term' syntax,(subst_elt Prims.list Prims.list,maybe_set_use_range)
                     FStar_Pervasives_Native.tuple2)
       FStar_Pervasives_Native.tuple2,term' syntax memo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tm_delayed _0 -> _0 
let (uu___is_Tm_meta : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_meta _0 -> true | uu____2240 -> false
  
let (__proj__Tm_meta__item___0 :
  term' -> (term' syntax,metadata) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Tm_meta _0 -> _0 
let (uu___is_Tm_lazy : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_lazy _0 -> true | uu____2272 -> false
  
let (__proj__Tm_lazy__item___0 : term' -> lazyinfo) =
  fun projectee  -> match projectee with | Tm_lazy _0 -> _0 
let (uu___is_Tm_quoted : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_quoted _0 -> true | uu____2292 -> false
  
let (__proj__Tm_quoted__item___0 :
  term' -> (term' syntax,quoteinfo) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Tm_quoted _0 -> _0 
let (uu___is_Tm_unknown : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tm_unknown  -> true | uu____2323 -> false
  
let (__proj__Mkctx_uvar__item__ctx_uvar_head :
  ctx_uvar ->
    (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,
      version) FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head = __fname__ctx_uvar_head;
        ctx_uvar_gamma = __fname__ctx_uvar_gamma;
        ctx_uvar_binders = __fname__ctx_uvar_binders;
        ctx_uvar_typ = __fname__ctx_uvar_typ;
        ctx_uvar_reason = __fname__ctx_uvar_reason;
        ctx_uvar_should_check = __fname__ctx_uvar_should_check;
        ctx_uvar_range = __fname__ctx_uvar_range;_} -> __fname__ctx_uvar_head
  
let (__proj__Mkctx_uvar__item__ctx_uvar_gamma :
  ctx_uvar -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head = __fname__ctx_uvar_head;
        ctx_uvar_gamma = __fname__ctx_uvar_gamma;
        ctx_uvar_binders = __fname__ctx_uvar_binders;
        ctx_uvar_typ = __fname__ctx_uvar_typ;
        ctx_uvar_reason = __fname__ctx_uvar_reason;
        ctx_uvar_should_check = __fname__ctx_uvar_should_check;
        ctx_uvar_range = __fname__ctx_uvar_range;_} ->
        __fname__ctx_uvar_gamma
  
let (__proj__Mkctx_uvar__item__ctx_uvar_binders :
  ctx_uvar ->
    (bv,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head = __fname__ctx_uvar_head;
        ctx_uvar_gamma = __fname__ctx_uvar_gamma;
        ctx_uvar_binders = __fname__ctx_uvar_binders;
        ctx_uvar_typ = __fname__ctx_uvar_typ;
        ctx_uvar_reason = __fname__ctx_uvar_reason;
        ctx_uvar_should_check = __fname__ctx_uvar_should_check;
        ctx_uvar_range = __fname__ctx_uvar_range;_} ->
        __fname__ctx_uvar_binders
  
let (__proj__Mkctx_uvar__item__ctx_uvar_typ : ctx_uvar -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head = __fname__ctx_uvar_head;
        ctx_uvar_gamma = __fname__ctx_uvar_gamma;
        ctx_uvar_binders = __fname__ctx_uvar_binders;
        ctx_uvar_typ = __fname__ctx_uvar_typ;
        ctx_uvar_reason = __fname__ctx_uvar_reason;
        ctx_uvar_should_check = __fname__ctx_uvar_should_check;
        ctx_uvar_range = __fname__ctx_uvar_range;_} -> __fname__ctx_uvar_typ
  
let (__proj__Mkctx_uvar__item__ctx_uvar_reason : ctx_uvar -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head = __fname__ctx_uvar_head;
        ctx_uvar_gamma = __fname__ctx_uvar_gamma;
        ctx_uvar_binders = __fname__ctx_uvar_binders;
        ctx_uvar_typ = __fname__ctx_uvar_typ;
        ctx_uvar_reason = __fname__ctx_uvar_reason;
        ctx_uvar_should_check = __fname__ctx_uvar_should_check;
        ctx_uvar_range = __fname__ctx_uvar_range;_} ->
        __fname__ctx_uvar_reason
  
let (__proj__Mkctx_uvar__item__ctx_uvar_should_check :
  ctx_uvar -> should_check_uvar) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head = __fname__ctx_uvar_head;
        ctx_uvar_gamma = __fname__ctx_uvar_gamma;
        ctx_uvar_binders = __fname__ctx_uvar_binders;
        ctx_uvar_typ = __fname__ctx_uvar_typ;
        ctx_uvar_reason = __fname__ctx_uvar_reason;
        ctx_uvar_should_check = __fname__ctx_uvar_should_check;
        ctx_uvar_range = __fname__ctx_uvar_range;_} ->
        __fname__ctx_uvar_should_check
  
let (__proj__Mkctx_uvar__item__ctx_uvar_range :
  ctx_uvar -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { ctx_uvar_head = __fname__ctx_uvar_head;
        ctx_uvar_gamma = __fname__ctx_uvar_gamma;
        ctx_uvar_binders = __fname__ctx_uvar_binders;
        ctx_uvar_typ = __fname__ctx_uvar_typ;
        ctx_uvar_reason = __fname__ctx_uvar_reason;
        ctx_uvar_should_check = __fname__ctx_uvar_should_check;
        ctx_uvar_range = __fname__ctx_uvar_range;_} ->
        __fname__ctx_uvar_range
  
let (uu___is_Pat_constant : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_constant _0 -> true | uu____2612 -> false
  
let (__proj__Pat_constant__item___0 : pat' -> sconst) =
  fun projectee  -> match projectee with | Pat_constant _0 -> _0 
let (uu___is_Pat_cons : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_cons _0 -> true | uu____2638 -> false
  
let (__proj__Pat_cons__item___0 :
  pat' ->
    (fv,(pat' withinfo_t,Prims.bool) FStar_Pervasives_Native.tuple2
          Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Pat_cons _0 -> _0 
let (uu___is_Pat_var : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_var _0 -> true | uu____2688 -> false
  
let (__proj__Pat_var__item___0 : pat' -> bv) =
  fun projectee  -> match projectee with | Pat_var _0 -> _0 
let (uu___is_Pat_wild : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_wild _0 -> true | uu____2702 -> false
  
let (__proj__Pat_wild__item___0 : pat' -> bv) =
  fun projectee  -> match projectee with | Pat_wild _0 -> _0 
let (uu___is_Pat_dot_term : pat' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_dot_term _0 -> true | uu____2722 -> false
  
let (__proj__Pat_dot_term__item___0 :
  pat' -> (bv,term' syntax) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Pat_dot_term _0 -> _0 
let (__proj__Mkletbinding__item__lbname :
  letbinding -> (bv,fv) FStar_Util.either) =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef; lbattrs = __fname__lbattrs;
        lbpos = __fname__lbpos;_} -> __fname__lbname
  
let (__proj__Mkletbinding__item__lbunivs :
  letbinding -> univ_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef; lbattrs = __fname__lbattrs;
        lbpos = __fname__lbpos;_} -> __fname__lbunivs
  
let (__proj__Mkletbinding__item__lbtyp : letbinding -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef; lbattrs = __fname__lbattrs;
        lbpos = __fname__lbpos;_} -> __fname__lbtyp
  
let (__proj__Mkletbinding__item__lbeff : letbinding -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef; lbattrs = __fname__lbattrs;
        lbpos = __fname__lbpos;_} -> __fname__lbeff
  
let (__proj__Mkletbinding__item__lbdef : letbinding -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef; lbattrs = __fname__lbattrs;
        lbpos = __fname__lbpos;_} -> __fname__lbdef
  
let (__proj__Mkletbinding__item__lbattrs :
  letbinding -> term' syntax Prims.list) =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef; lbattrs = __fname__lbattrs;
        lbpos = __fname__lbpos;_} -> __fname__lbattrs
  
let (__proj__Mkletbinding__item__lbpos : letbinding -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef; lbattrs = __fname__lbattrs;
        lbpos = __fname__lbpos;_} -> __fname__lbpos
  
let (__proj__Mkquoteinfo__item__qkind : quoteinfo -> quote_kind) =
  fun projectee  ->
    match projectee with
    | { qkind = __fname__qkind; antiquotes = __fname__antiquotes;_} ->
        __fname__qkind
  
let (__proj__Mkquoteinfo__item__antiquotes :
  quoteinfo -> (bv,term' syntax) FStar_Pervasives_Native.tuple2 Prims.list) =
  fun projectee  ->
    match projectee with
    | { qkind = __fname__qkind; antiquotes = __fname__antiquotes;_} ->
        __fname__antiquotes
  
let (__proj__Mkcomp_typ__item__comp_univs : comp_typ -> universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ ->
    (term' syntax,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_args
  
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__flags
  
let (uu___is_Total : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Total _0 -> true | uu____3166 -> false
  
let (__proj__Total__item___0 :
  comp' ->
    (term' syntax,universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Total _0 -> _0 
let (uu___is_GTotal : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTotal _0 -> true | uu____3212 -> false
  
let (__proj__GTotal__item___0 :
  comp' ->
    (term' syntax,universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTotal _0 -> _0 
let (uu___is_Comp : comp' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____3250 -> false
  
let (__proj__Comp__item___0 : comp' -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (uu___is_TOTAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____3263 -> false
  
let (uu___is_MLEFFECT : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____3269 -> false
  
let (uu___is_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____3275 -> false
  
let (uu___is_PARTIAL_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____3281 -> false
  
let (uu___is_SOMETRIVIAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____3287 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____3293 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____3299 -> false
  
let (uu___is_LEMMA : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____3305 -> false
  
let (uu___is_CPS : cflags -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____3311 -> false 
let (uu___is_DECREASES : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____3320 -> false
  
let (__proj__DECREASES__item___0 : cflags -> term' syntax) =
  fun projectee  -> match projectee with | DECREASES _0 -> _0 
let (uu___is_Meta_pattern : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_pattern _0 -> true | uu____3352 -> false
  
let (__proj__Meta_pattern__item___0 :
  metadata ->
    (term' syntax,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  = fun projectee  -> match projectee with | Meta_pattern _0 -> _0 
let (uu___is_Meta_named : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_named _0 -> true | uu____3402 -> false
  
let (__proj__Meta_named__item___0 : metadata -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Meta_named _0 -> _0 
let (uu___is_Meta_labeled : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_labeled _0 -> true | uu____3422 -> false
  
let (__proj__Meta_labeled__item___0 :
  metadata ->
    (Prims.string,FStar_Range.range,Prims.bool)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta_labeled _0 -> _0 
let (uu___is_Meta_desugared : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_desugared _0 -> true | uu____3454 -> false
  
let (__proj__Meta_desugared__item___0 : metadata -> meta_source_info) =
  fun projectee  -> match projectee with | Meta_desugared _0 -> _0 
let (uu___is_Meta_monadic : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_monadic _0 -> true | uu____3474 -> false
  
let (__proj__Meta_monadic__item___0 :
  metadata -> (monad_name,term' syntax) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Meta_monadic _0 -> _0 
let (uu___is_Meta_monadic_lift : metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_monadic_lift _0 -> true | uu____3514 -> false
  
let (__proj__Meta_monadic_lift__item___0 :
  metadata ->
    (monad_name,monad_name,term' syntax) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta_monadic_lift _0 -> _0 
let (uu___is_Sequence : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sequence  -> true | uu____3551 -> false
  
let (uu___is_Primop : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primop  -> true | uu____3557 -> false
  
let (uu___is_Masked_effect : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Masked_effect  -> true | uu____3563 -> false
  
let (uu___is_Meta_smt_pat : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta_smt_pat  -> true | uu____3569 -> false
  
let (uu___is_Mutable_alloc : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mutable_alloc  -> true | uu____3575 -> false
  
let (uu___is_Mutable_rval : meta_source_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mutable_rval  -> true | uu____3581 -> false
  
let (uu___is_Data_ctor : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Data_ctor  -> true | uu____3587 -> false
  
let (uu___is_Record_projector : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_projector _0 -> true | uu____3598 -> false
  
let (__proj__Record_projector__item___0 :
  fv_qual ->
    (FStar_Ident.lident,FStar_Ident.ident) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Record_projector _0 -> _0 
let (uu___is_Record_ctor : fv_qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_ctor _0 -> true | uu____3630 -> false
  
let (__proj__Record_ctor__item___0 :
  fv_qual ->
    (FStar_Ident.lident,FStar_Ident.ident Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Record_ctor _0 -> _0 
let (uu___is_DB : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | DB _0 -> true | uu____3666 -> false
  
let (__proj__DB__item___0 :
  subst_elt -> (Prims.int,bv) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | DB _0 -> _0 
let (uu___is_NM : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | NM _0 -> true | uu____3696 -> false
  
let (__proj__NM__item___0 :
  subst_elt -> (bv,Prims.int) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | NM _0 -> _0 
let (uu___is_NT : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | NT _0 -> true | uu____3728 -> false
  
let (__proj__NT__item___0 :
  subst_elt -> (bv,term' syntax) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | NT _0 -> _0 
let (uu___is_UN : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UN _0 -> true | uu____3764 -> false
  
let (__proj__UN__item___0 :
  subst_elt -> (Prims.int,universe) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | UN _0 -> _0 
let (uu___is_UD : subst_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UD _0 -> true | uu____3794 -> false
  
let (__proj__UD__item___0 :
  subst_elt -> (univ_name,Prims.int) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | UD _0 -> _0 
let __proj__Mksyntax__item__n : 'a . 'a syntax -> 'a =
  fun projectee  ->
    match projectee with
    | { n = __fname__n; pos = __fname__pos; vars = __fname__vars;_} ->
        __fname__n
  
let __proj__Mksyntax__item__pos : 'a . 'a syntax -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { n = __fname__n; pos = __fname__pos; vars = __fname__vars;_} ->
        __fname__pos
  
let __proj__Mksyntax__item__vars : 'a . 'a syntax -> free_vars memo =
  fun projectee  ->
    match projectee with
    | { n = __fname__n; pos = __fname__pos; vars = __fname__vars;_} ->
        __fname__vars
  
let (__proj__Mkbv__item__ppname : bv -> FStar_Ident.ident) =
  fun projectee  ->
    match projectee with
    | { ppname = __fname__ppname; index = __fname__index;
        sort = __fname__sort;_} -> __fname__ppname
  
let (__proj__Mkbv__item__index : bv -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { ppname = __fname__ppname; index = __fname__index;
        sort = __fname__sort;_} -> __fname__index
  
let (__proj__Mkbv__item__sort : bv -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { ppname = __fname__ppname; index = __fname__index;
        sort = __fname__sort;_} -> __fname__sort
  
let (__proj__Mkfv__item__fv_name : fv -> var) =
  fun projectee  ->
    match projectee with
    | { fv_name = __fname__fv_name; fv_delta = __fname__fv_delta;
        fv_qual = __fname__fv_qual;_} -> __fname__fv_name
  
let (__proj__Mkfv__item__fv_delta : fv -> delta_depth) =
  fun projectee  ->
    match projectee with
    | { fv_name = __fname__fv_name; fv_delta = __fname__fv_delta;
        fv_qual = __fname__fv_qual;_} -> __fname__fv_delta
  
let (__proj__Mkfv__item__fv_qual :
  fv -> fv_qual FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { fv_name = __fname__fv_name; fv_delta = __fname__fv_delta;
        fv_qual = __fname__fv_qual;_} -> __fname__fv_qual
  
let (__proj__Mkfree_vars__item__free_names : free_vars -> bv Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} -> __fname__free_names
  
let (__proj__Mkfree_vars__item__free_uvars :
  free_vars -> ctx_uvar Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} -> __fname__free_uvars
  
let (__proj__Mkfree_vars__item__free_univs :
  free_vars -> universe_uvar Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} -> __fname__free_univs
  
let (__proj__Mkfree_vars__item__free_univ_names :
  free_vars -> univ_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} ->
        __fname__free_univ_names
  
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} ->
        __fname__residual_effect
  
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> term' syntax FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} -> __fname__residual_typ
  
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} ->
        __fname__residual_flags
  
let (__proj__Mklazyinfo__item__blob : lazyinfo -> FStar_Dyn.dyn) =
  fun projectee  ->
    match projectee with
    | { blob = __fname__blob; lkind = __fname__lkind; ltyp = __fname__ltyp;
        rng = __fname__rng;_} -> __fname__blob
  
let (__proj__Mklazyinfo__item__lkind : lazyinfo -> lazy_kind) =
  fun projectee  ->
    match projectee with
    | { blob = __fname__blob; lkind = __fname__lkind; ltyp = __fname__ltyp;
        rng = __fname__rng;_} -> __fname__lkind
  
let (__proj__Mklazyinfo__item__ltyp : lazyinfo -> term' syntax) =
  fun projectee  ->
    match projectee with
    | { blob = __fname__blob; lkind = __fname__lkind; ltyp = __fname__ltyp;
        rng = __fname__rng;_} -> __fname__ltyp
  
let (__proj__Mklazyinfo__item__rng : lazyinfo -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { blob = __fname__blob; lkind = __fname__lkind; ltyp = __fname__ltyp;
        rng = __fname__rng;_} -> __fname__rng
  
let (uu___is_BadLazy : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | BadLazy  -> true | uu____4165 -> false
  
let (uu___is_Lazy_bv : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_bv  -> true | uu____4171 -> false
  
let (uu___is_Lazy_binder : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_binder  -> true | uu____4177 -> false
  
let (uu___is_Lazy_fvar : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_fvar  -> true | uu____4183 -> false
  
let (uu___is_Lazy_comp : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_comp  -> true | uu____4189 -> false
  
let (uu___is_Lazy_env : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_env  -> true | uu____4195 -> false
  
let (uu___is_Lazy_proofstate : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_proofstate  -> true | uu____4201 -> false
  
let (uu___is_Lazy_sigelt : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_sigelt  -> true | uu____4207 -> false
  
let (uu___is_Lazy_uvar : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_uvar  -> true | uu____4213 -> false
  
let (uu___is_Lazy_embedding : lazy_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy_embedding _0 -> true | uu____4228 -> false
  
let (__proj__Lazy_embedding__item___0 :
  lazy_kind ->
    (emb_typ,term' syntax FStar_Common.thunk) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Lazy_embedding _0 -> _0 
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____4266 -> false
  
let (__proj__Binding_var__item___0 : binding -> bv) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____4292 -> false
  
let (__proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident,(univ_name Prims.list,term' syntax)
                          FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____4342 -> false
  
let (__proj__Binding_univ__item___0 : binding -> univ_name) =
  fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit _0 -> true | uu____4356 -> false
  
let (__proj__Implicit__item___0 : arg_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Implicit _0 -> _0 
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____4372 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term' syntax) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____4391 -> false
  
type subst_ts =
  (subst_elt Prims.list Prims.list,maybe_set_use_range)
    FStar_Pervasives_Native.tuple2
type ctx_uvar_and_subst =
  (ctx_uvar,(subst_elt Prims.list Prims.list,maybe_set_use_range)
              FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2
type term = term' syntax
type uvar =
  (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,
    version) FStar_Pervasives_Native.tuple2
type uvars = ctx_uvar FStar_Util.set
type pat = pat' withinfo_t
type branch =
  (pat' withinfo_t,term' syntax FStar_Pervasives_Native.option,term' syntax)
    FStar_Pervasives_Native.tuple3
type comp = comp' syntax
type ascription =
  ((term' syntax,comp' syntax) FStar_Util.either,term' syntax
                                                   FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2
type antiquotations =
  (bv,term' syntax) FStar_Pervasives_Native.tuple2 Prims.list
type typ = term' syntax
type aqual = arg_qualifier FStar_Pervasives_Native.option
type arg =
  (term' syntax,arg_qualifier FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2
type args =
  (term' syntax,arg_qualifier FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list
type binder =
  (bv,arg_qualifier FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2
type binders =
  (bv,arg_qualifier FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list
type lbname = (bv,fv) FStar_Util.either
type letbindings =
  (Prims.bool,letbinding Prims.list) FStar_Pervasives_Native.tuple2
type freenames = bv FStar_Util.set
type attribute = term' syntax
type tscheme =
  (univ_name Prims.list,term' syntax) FStar_Pervasives_Native.tuple2
type gamma = binding Prims.list
type lcomp =
  {
  eff_name: FStar_Ident.lident ;
  res_typ: typ ;
  cflags: cflags Prims.list ;
  comp_thunk: (unit -> comp,comp) FStar_Util.either FStar_ST.ref }
let (__proj__Mklcomp__item__eff_name : lcomp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp_thunk = __fname__comp_thunk;_} ->
        __fname__eff_name
  
let (__proj__Mklcomp__item__res_typ : lcomp -> typ) =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp_thunk = __fname__comp_thunk;_} ->
        __fname__res_typ
  
let (__proj__Mklcomp__item__cflags : lcomp -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp_thunk = __fname__comp_thunk;_} ->
        __fname__cflags
  
let (__proj__Mklcomp__item__comp_thunk :
  lcomp -> (unit -> comp,comp) FStar_Util.either FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp_thunk = __fname__comp_thunk;_} ->
        __fname__comp_thunk
  
let (lazy_chooser :
  (lazy_kind -> lazyinfo -> term) FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (mk_lcomp :
  FStar_Ident.lident -> typ -> cflags Prims.list -> (unit -> comp) -> lcomp)
  =
  fun eff_name  ->
    fun res_typ  ->
      fun cflags  ->
        fun comp_thunk  ->
          let uu____4809 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____4809 }
  
let (lcomp_comp : lcomp -> comp) =
  fun lc  ->
    let uu____4856 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____4856 with
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
  | Projector of (FStar_Ident.lident,FStar_Ident.ident)
  FStar_Pervasives_Native.tuple2 
  | RecordType of (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
  FStar_Pervasives_Native.tuple2 
  | RecordConstructor of
  (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Action of FStar_Ident.lident 
  | ExceptionConstructor 
  | HasMaskedEffect 
  | Effect 
  | OnlyName 
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____5005 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____5011 -> false 
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____5017 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____5023 -> false
  
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____5029 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____5035 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____5041 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____5047 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____5053 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____5059 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____5065 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____5071 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____5077 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____5083 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____5090 -> false
  
let (__proj__Reflectable__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Reflectable _0 -> _0 
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discriminator _0 -> true | uu____5104 -> false
  
let (__proj__Discriminator__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Discriminator _0 -> _0 
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____5122 -> false
  
let (__proj__Projector__item___0 :
  qualifier ->
    (FStar_Ident.lident,FStar_Ident.ident) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | RecordType _0 -> true | uu____5156 -> false
  
let (__proj__RecordType__item___0 :
  qualifier ->
    (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | RecordType _0 -> _0 
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | RecordConstructor _0 -> true | uu____5202 -> false
  
let (__proj__RecordConstructor__item___0 :
  qualifier ->
    (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | RecordConstructor _0 -> _0 
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Action _0 -> true | uu____5240 -> false
  
let (__proj__Action__item___0 : qualifier -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | Action _0 -> _0 
let (uu___is_ExceptionConstructor : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ExceptionConstructor  -> true
    | uu____5253 -> false
  
let (uu___is_HasMaskedEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | HasMaskedEffect  -> true | uu____5259 -> false
  
let (uu___is_Effect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect  -> true | uu____5265 -> false
  
let (uu___is_OnlyName : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | OnlyName  -> true | uu____5271 -> false
  
type tycon = (FStar_Ident.lident,binders,typ) FStar_Pervasives_Native.tuple3
type monad_abbrev = {
  mabbrev: FStar_Ident.lident ;
  parms: binders ;
  def: typ }
let (__proj__Mkmonad_abbrev__item__mabbrev :
  monad_abbrev -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { mabbrev = __fname__mabbrev; parms = __fname__parms;
        def = __fname__def;_} -> __fname__mabbrev
  
let (__proj__Mkmonad_abbrev__item__parms : monad_abbrev -> binders) =
  fun projectee  ->
    match projectee with
    | { mabbrev = __fname__mabbrev; parms = __fname__parms;
        def = __fname__def;_} -> __fname__parms
  
let (__proj__Mkmonad_abbrev__item__def : monad_abbrev -> typ) =
  fun projectee  ->
    match projectee with
    | { mabbrev = __fname__mabbrev; parms = __fname__parms;
        def = __fname__def;_} -> __fname__def
  
type sub_eff =
  {
  source: FStar_Ident.lident ;
  target: FStar_Ident.lident ;
  lift_wp: tscheme FStar_Pervasives_Native.option ;
  lift: tscheme FStar_Pervasives_Native.option }
let (__proj__Mksub_eff__item__source : sub_eff -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} ->
        __fname__source
  
let (__proj__Mksub_eff__item__target : sub_eff -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} ->
        __fname__target
  
let (__proj__Mksub_eff__item__lift_wp :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} ->
        __fname__lift_wp
  
let (__proj__Mksub_eff__item__lift :
  sub_eff -> tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} -> __fname__lift
  
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
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_name
  
let (__proj__Mkaction__item__action_unqualified_name :
  action -> FStar_Ident.ident) =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} ->
        __fname__action_unqualified_name
  
let (__proj__Mkaction__item__action_univs : action -> univ_names) =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_univs
  
let (__proj__Mkaction__item__action_params : action -> binders) =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_params
  
let (__proj__Mkaction__item__action_defn : action -> term) =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_defn
  
let (__proj__Mkaction__item__action_typ : action -> typ) =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_typ
  
type eff_decl =
  {
  cattributes: cflags Prims.list ;
  mname: FStar_Ident.lident ;
  univs: univ_names ;
  binders: binders ;
  signature: term ;
  ret_wp: tscheme ;
  bind_wp: tscheme ;
  if_then_else: tscheme ;
  ite_wp: tscheme ;
  stronger: tscheme ;
  close_wp: tscheme ;
  assert_p: tscheme ;
  assume_p: tscheme ;
  null_wp: tscheme ;
  trivial: tscheme ;
  repr: term ;
  return_repr: tscheme ;
  bind_repr: tscheme ;
  actions: action Prims.list ;
  eff_attrs: attribute Prims.list }
let (__proj__Mkeff_decl__item__cattributes : eff_decl -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__cattributes
  
let (__proj__Mkeff_decl__item__mname : eff_decl -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__mname
  
let (__proj__Mkeff_decl__item__univs : eff_decl -> univ_names) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__univs
  
let (__proj__Mkeff_decl__item__binders : eff_decl -> binders) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__binders
  
let (__proj__Mkeff_decl__item__signature : eff_decl -> term) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__signature
  
let (__proj__Mkeff_decl__item__ret_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__ret_wp
  
let (__proj__Mkeff_decl__item__bind_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__bind_wp
  
let (__proj__Mkeff_decl__item__if_then_else : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__if_then_else
  
let (__proj__Mkeff_decl__item__ite_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__ite_wp
  
let (__proj__Mkeff_decl__item__stronger : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__stronger
  
let (__proj__Mkeff_decl__item__close_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__close_wp
  
let (__proj__Mkeff_decl__item__assert_p : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__assert_p
  
let (__proj__Mkeff_decl__item__assume_p : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__assume_p
  
let (__proj__Mkeff_decl__item__null_wp : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__null_wp
  
let (__proj__Mkeff_decl__item__trivial : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__trivial
  
let (__proj__Mkeff_decl__item__repr : eff_decl -> term) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__repr
  
let (__proj__Mkeff_decl__item__return_repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__return_repr
  
let (__proj__Mkeff_decl__item__bind_repr : eff_decl -> tscheme) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__bind_repr
  
let (__proj__Mkeff_decl__item__actions : eff_decl -> action Prims.list) =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__actions
  
let (__proj__Mkeff_decl__item__eff_attrs : eff_decl -> attribute Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { cattributes = __fname__cattributes; mname = __fname__mname;
        univs = __fname__univs; binders = __fname__binders;
        signature = __fname__signature; ret_wp = __fname__ret_wp;
        bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else;
        ite_wp = __fname__ite_wp; stronger = __fname__stronger;
        close_wp = __fname__close_wp; assert_p = __fname__assert_p;
        assume_p = __fname__assume_p; null_wp = __fname__null_wp;
        trivial = __fname__trivial; repr = __fname__repr;
        return_repr = __fname__return_repr; bind_repr = __fname__bind_repr;
        actions = __fname__actions; eff_attrs = __fname__eff_attrs;_} ->
        __fname__eff_attrs
  
type sig_metadata =
  {
  sigmeta_active: Prims.bool ;
  sigmeta_fact_db_ids: Prims.string Prims.list }
let (__proj__Mksig_metadata__item__sigmeta_active :
  sig_metadata -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { sigmeta_active = __fname__sigmeta_active;
        sigmeta_fact_db_ids = __fname__sigmeta_fact_db_ids;_} ->
        __fname__sigmeta_active
  
let (__proj__Mksig_metadata__item__sigmeta_fact_db_ids :
  sig_metadata -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigmeta_active = __fname__sigmeta_active;
        sigmeta_fact_db_ids = __fname__sigmeta_fact_db_ids;_} ->
        __fname__sigmeta_fact_db_ids
  
type sigelt' =
  | Sig_inductive_typ of
  (FStar_Ident.lident,univ_names,binders,typ,FStar_Ident.lident Prims.list,
  FStar_Ident.lident Prims.list) FStar_Pervasives_Native.tuple6 
  | Sig_bundle of (sigelt Prims.list,FStar_Ident.lident Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Sig_datacon of
  (FStar_Ident.lident,univ_names,typ,FStar_Ident.lident,Prims.int,FStar_Ident.lident
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple6 
  | Sig_declare_typ of (FStar_Ident.lident,univ_names,typ)
  FStar_Pervasives_Native.tuple3 
  | Sig_let of (letbindings,FStar_Ident.lident Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Sig_main of term 
  | Sig_assume of (FStar_Ident.lident,univ_names,formula)
  FStar_Pervasives_Native.tuple3 
  | Sig_new_effect of eff_decl 
  | Sig_new_effect_for_free of eff_decl 
  | Sig_sub_effect of sub_eff 
  | Sig_effect_abbrev of
  (FStar_Ident.lident,univ_names,binders,comp,cflags Prims.list)
  FStar_Pervasives_Native.tuple5 
  | Sig_pragma of pragma 
  | Sig_splice of (FStar_Ident.lident Prims.list,term)
  FStar_Pervasives_Native.tuple2 
and sigelt =
  {
  sigel: sigelt' ;
  sigrng: FStar_Range.range ;
  sigquals: qualifier Prims.list ;
  sigmeta: sig_metadata ;
  sigattrs: attribute Prims.list }
let (uu___is_Sig_inductive_typ : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_inductive_typ _0 -> true | uu____6459 -> false
  
let (__proj__Sig_inductive_typ__item___0 :
  sigelt' ->
    (FStar_Ident.lident,univ_names,binders,typ,FStar_Ident.lident Prims.list,
      FStar_Ident.lident Prims.list) FStar_Pervasives_Native.tuple6)
  = fun projectee  -> match projectee with | Sig_inductive_typ _0 -> _0 
let (uu___is_Sig_bundle : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_bundle _0 -> true | uu____6529 -> false
  
let (__proj__Sig_bundle__item___0 :
  sigelt' ->
    (sigelt Prims.list,FStar_Ident.lident Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Sig_bundle _0 -> _0 
let (uu___is_Sig_datacon : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_datacon _0 -> true | uu____6581 -> false
  
let (__proj__Sig_datacon__item___0 :
  sigelt' ->
    (FStar_Ident.lident,univ_names,typ,FStar_Ident.lident,Prims.int,FStar_Ident.lident
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple6)
  = fun projectee  -> match projectee with | Sig_datacon _0 -> _0 
let (uu___is_Sig_declare_typ : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_declare_typ _0 -> true | uu____6643 -> false
  
let (__proj__Sig_declare_typ__item___0 :
  sigelt' ->
    (FStar_Ident.lident,univ_names,typ) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Sig_declare_typ _0 -> _0 
let (uu___is_Sig_let : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_let _0 -> true | uu____6681 -> false
  
let (__proj__Sig_let__item___0 :
  sigelt' ->
    (letbindings,FStar_Ident.lident Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Sig_let _0 -> _0 
let (uu___is_Sig_main : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_main _0 -> true | uu____6713 -> false
  
let (__proj__Sig_main__item___0 : sigelt' -> term) =
  fun projectee  -> match projectee with | Sig_main _0 -> _0 
let (uu___is_Sig_assume : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_assume _0 -> true | uu____6733 -> false
  
let (__proj__Sig_assume__item___0 :
  sigelt' ->
    (FStar_Ident.lident,univ_names,formula) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Sig_assume _0 -> _0 
let (uu___is_Sig_new_effect : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_new_effect _0 -> true | uu____6765 -> false
  
let (__proj__Sig_new_effect__item___0 : sigelt' -> eff_decl) =
  fun projectee  -> match projectee with | Sig_new_effect _0 -> _0 
let (uu___is_Sig_new_effect_for_free : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Sig_new_effect_for_free _0 -> true
    | uu____6779 -> false
  
let (__proj__Sig_new_effect_for_free__item___0 : sigelt' -> eff_decl) =
  fun projectee  -> match projectee with | Sig_new_effect_for_free _0 -> _0 
let (uu___is_Sig_sub_effect : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_sub_effect _0 -> true | uu____6793 -> false
  
let (__proj__Sig_sub_effect__item___0 : sigelt' -> sub_eff) =
  fun projectee  -> match projectee with | Sig_sub_effect _0 -> _0 
let (uu___is_Sig_effect_abbrev : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_effect_abbrev _0 -> true | uu____6819 -> false
  
let (__proj__Sig_effect_abbrev__item___0 :
  sigelt' ->
    (FStar_Ident.lident,univ_names,binders,comp,cflags Prims.list)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Sig_effect_abbrev _0 -> _0 
let (uu___is_Sig_pragma : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_pragma _0 -> true | uu____6869 -> false
  
let (__proj__Sig_pragma__item___0 : sigelt' -> pragma) =
  fun projectee  -> match projectee with | Sig_pragma _0 -> _0 
let (uu___is_Sig_splice : sigelt' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sig_splice _0 -> true | uu____6889 -> false
  
let (__proj__Sig_splice__item___0 :
  sigelt' ->
    (FStar_Ident.lident Prims.list,term) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Sig_splice _0 -> _0 
let (__proj__Mksigelt__item__sigel : sigelt -> sigelt') =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;
        sigattrs = __fname__sigattrs;_} -> __fname__sigel
  
let (__proj__Mksigelt__item__sigrng : sigelt -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;
        sigattrs = __fname__sigattrs;_} -> __fname__sigrng
  
let (__proj__Mksigelt__item__sigquals : sigelt -> qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;
        sigattrs = __fname__sigattrs;_} -> __fname__sigquals
  
let (__proj__Mksigelt__item__sigmeta : sigelt -> sig_metadata) =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;
        sigattrs = __fname__sigattrs;_} -> __fname__sigmeta
  
let (__proj__Mksigelt__item__sigattrs : sigelt -> attribute Prims.list) =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;
        sigattrs = __fname__sigattrs;_} -> __fname__sigattrs
  
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
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__name
  
let (__proj__Mkmodul__item__declarations : modul -> sigelts) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__declarations
  
let (__proj__Mkmodul__item__exports : modul -> sigelts) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__exports
  
let (__proj__Mkmodul__item__is_interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__is_interface
  
let (mod_name : modul -> FStar_Ident.lident) = fun m  -> m.name 
type path = Prims.string Prims.list
type subst_t = subst_elt Prims.list
type 'a mk_t_a =
  unit FStar_Pervasives_Native.option -> FStar_Range.range -> 'a syntax
type mk_t = term' mk_t_a
let (contains_reflectable : qualifier Prims.list -> Prims.bool) =
  fun l  ->
    FStar_Util.for_some
      (fun uu___83_7089  ->
         match uu___83_7089 with
         | Reflectable uu____7090 -> true
         | uu____7091 -> false) l
  
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
      if i = (Prims.parse_int "0") then x.index - y.index else i
  
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
      let uu___90_7177 = x  in
      let uu____7178 =
        FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____7178;
        index = (uu___90_7177.index);
        sort = (uu___90_7177.sort)
      }
  
let (on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo) =
  fun f  ->
    fun qi  ->
      let aq =
        FStar_List.map
          (fun uu____7213  ->
             match uu____7213 with
             | (bv,t) -> let uu____7224 = f t  in (bv, uu____7224))
          qi.antiquotes
         in
      let uu___91_7225 = qi  in
      { qkind = (uu___91_7225.qkind); antiquotes = aq }
  
let (lookup_aq : bv -> antiquotations -> term FStar_Pervasives_Native.option)
  =
  fun bv  ->
    fun aq  ->
      let uu____7240 =
        FStar_List.tryFind
          (fun uu____7258  ->
             match uu____7258 with | (bv',uu____7266) -> bv_eq bv bv') aq
         in
      match uu____7240 with
      | FStar_Pervasives_Native.Some (uu____7273,e) ->
          FStar_Pervasives_Native.Some e
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let syn :
  'Auu____7303 'Auu____7304 'Auu____7305 .
    'Auu____7303 ->
      'Auu____7304 ->
        ('Auu____7304 -> 'Auu____7303 -> 'Auu____7305) -> 'Auu____7305
  = fun p  -> fun k  -> fun f  -> f k p 
let mk_fvs :
  'Auu____7346 .
    unit -> 'Auu____7346 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____7355  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let mk_uvs :
  'Auu____7373 .
    unit -> 'Auu____7373 FStar_Pervasives_Native.option FStar_ST.ref
  = fun uu____7382  -> FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (new_bv_set : unit -> bv FStar_Util.set) =
  fun uu____7391  -> FStar_Util.new_set order_bv 
let (new_fv_set : unit -> FStar_Ident.lident FStar_Util.set) =
  fun uu____7400  -> FStar_Util.new_set order_fv 
let (order_univ_name : univ_name -> univ_name -> Prims.int) =
  fun x  ->
    fun y  ->
      let uu____7413 = FStar_Ident.text_of_id x  in
      let uu____7414 = FStar_Ident.text_of_id y  in
      FStar_String.compare uu____7413 uu____7414
  
let (new_universe_names_set : unit -> univ_name FStar_Util.set) =
  fun uu____7421  -> FStar_Util.new_set order_univ_name 
let (eq_binding : binding -> binding -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with
      | (Binding_var bv1,Binding_var bv2) -> bv_eq bv1 bv2
      | (Binding_lid (lid1,uu____7437),Binding_lid (lid2,uu____7439)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (Binding_univ u1,Binding_univ u2) -> FStar_Ident.ident_equals u1 u2
      | uu____7474 -> false
  
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
    fun uu____7527  ->
      fun r  ->
        let uu____7531 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        { n = t; pos = r; vars = uu____7531 }
  
let (bv_to_tm : bv -> term) =
  fun bv  ->
    let uu____7563 = range_of_bv bv  in
    mk (Tm_bvar bv) FStar_Pervasives_Native.None uu____7563
  
let (bv_to_name : bv -> term) =
  fun bv  ->
    let uu____7569 = range_of_bv bv  in
    mk (Tm_name bv) FStar_Pervasives_Native.None uu____7569
  
let (mk_Tm_app : term -> args -> mk_t) =
  fun t1  ->
    fun args  ->
      fun k  ->
        fun p  ->
          match args with
          | [] -> t1
          | uu____7598 ->
              mk (Tm_app (t1, args)) FStar_Pervasives_Native.None p
  
let (mk_Tm_uinst : term -> universes -> term) =
  fun t  ->
    fun uu___84_7622  ->
      match uu___84_7622 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____7624 ->
               mk (Tm_uinst (t, us)) FStar_Pervasives_Native.None t.pos
           | uu____7627 -> failwith "Unexpected universe instantiation")
  
let (extend_app_n : term -> args -> mk_t) =
  fun t  ->
    fun args'  ->
      fun kopt  ->
        fun r  ->
          match t.n with
          | Tm_app (head1,args) ->
              mk_Tm_app head1 (FStar_List.append args args') kopt r
          | uu____7688 -> mk_Tm_app t args' kopt r
  
let (extend_app : term -> arg -> mk_t) =
  fun t  -> fun arg  -> fun kopt  -> fun r  -> extend_app_n t [arg] kopt r 
let (mk_Tm_delayed :
  (term,subst_ts) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun lr  ->
    fun pos  ->
      let uu____7747 =
        let uu____7754 =
          let uu____7755 =
            let uu____7778 = FStar_Util.mk_ref FStar_Pervasives_Native.None
               in
            (lr, uu____7778)  in
          Tm_delayed uu____7755  in
        mk uu____7754  in
      uu____7747 FStar_Pervasives_Native.None pos
  
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
  (lbname,univ_name Prims.list,FStar_Ident.lident,typ,term,FStar_Range.range)
    FStar_Pervasives_Native.tuple6 -> letbinding)
  =
  fun uu____7901  ->
    match uu____7901 with
    | (x,univs,eff,t,e,pos) ->
        {
          lbname = x;
          lbunivs = univs;
          lbtyp = t;
          lbeff = eff;
          lbdef = e;
          lbattrs = [];
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
    | uu____7966 -> false
  
let (is_type : term -> Prims.bool) =
  fun t  -> match t.n with | Tm_type uu____7972 -> true | uu____7973 -> false 
let (null_id : FStar_Ident.ident) =
  FStar_Ident.mk_ident ("_", FStar_Range.dummyRange) 
let (null_bv : term -> bv) =
  fun k  -> { ppname = null_id; index = (Prims.parse_int "0"); sort = k } 
let (mk_binder : bv -> binder) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (null_binder : term -> binder) =
  fun t  ->
    let uu____7991 = null_bv t  in (uu____7991, FStar_Pervasives_Native.None)
  
let (imp_tag : arg_qualifier) = Implicit false 
let (iarg : term -> arg) =
  fun t  -> (t, (FStar_Pervasives_Native.Some imp_tag)) 
let (as_arg : term -> arg) = fun t  -> (t, FStar_Pervasives_Native.None) 
let (is_null_bv : bv -> Prims.bool) =
  fun b  -> (b.ppname).FStar_Ident.idText = null_id.FStar_Ident.idText 
let (is_null_binder : binder -> Prims.bool) =
  fun b  -> is_null_bv (FStar_Pervasives_Native.fst b) 
let (is_top_level : letbinding Prims.list -> Prims.bool) =
  fun uu___85_8030  ->
    match uu___85_8030 with
    | { lbname = FStar_Util.Inr uu____8033; lbunivs = uu____8034;
        lbtyp = uu____8035; lbeff = uu____8036; lbdef = uu____8037;
        lbattrs = uu____8038; lbpos = uu____8039;_}::uu____8040 -> true
    | uu____8053 -> false
  
let (freenames_of_binders : binders -> freenames) =
  fun bs  ->
    FStar_List.fold_right
      (fun uu____8073  ->
         fun out  ->
           match uu____8073 with | (x,uu____8086) -> FStar_Util.set_add x out)
      bs no_names
  
let (binders_of_list : bv Prims.list -> binders) =
  fun fvs  ->
    FStar_All.pipe_right fvs
      (FStar_List.map (fun t  -> (t, FStar_Pervasives_Native.None)))
  
let (binders_of_freenames : freenames -> binders) =
  fun fvs  ->
    let uu____8117 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____8117 binders_of_list
  
let (is_implicit : aqual -> Prims.bool) =
  fun uu___86_8126  ->
    match uu___86_8126 with
    | FStar_Pervasives_Native.Some (Implicit uu____8127) -> true
    | uu____8128 -> false
  
let (as_implicit : Prims.bool -> aqual) =
  fun uu___87_8133  ->
    if uu___87_8133
    then FStar_Pervasives_Native.Some imp_tag
    else FStar_Pervasives_Native.None
  
let (pat_bvs : pat -> bv Prims.list) =
  fun p  ->
    let rec aux b p1 =
      match p1.v with
      | Pat_dot_term uu____8167 -> b
      | Pat_constant uu____8174 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____8177,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____8208  ->
                 match uu____8208 with | (p2,uu____8220) -> aux b1 p2) b pats
       in
    let uu____8225 = aux [] p  in
    FStar_All.pipe_left FStar_List.rev uu____8225
  
let (gen_reset :
  (unit -> Prims.int,unit -> unit) FStar_Pervasives_Native.tuple2) =
  let x = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let gen1 uu____8250 = FStar_Util.incr x; FStar_ST.op_Bang x  in
  let reset uu____8331 = FStar_ST.op_Colon_Equals x (Prims.parse_int "0")  in
  (gen1, reset) 
let (next_id : unit -> Prims.int) = FStar_Pervasives_Native.fst gen_reset 
let (reset_gensym : unit -> unit) = FStar_Pervasives_Native.snd gen_reset 
let (range_of_ropt :
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Range.range) =
  fun uu___88_8405  ->
    match uu___88_8405 with
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
        let uu____8440 = next_id ()  in
        { ppname = id1; index = uu____8440; sort = t }
  
let (new_bv : FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv)
  = fun ropt  -> fun t  -> gen_bv FStar_Ident.reserved_prefix ropt t 
let (freshen_bv : bv -> bv) =
  fun bv  ->
    let uu____8460 = is_null_bv bv  in
    if uu____8460
    then
      let uu____8461 =
        let uu____8464 = range_of_bv bv  in
        FStar_Pervasives_Native.Some uu____8464  in
      new_bv uu____8461 bv.sort
    else
      (let uu___92_8466 = bv  in
       let uu____8467 = next_id ()  in
       {
         ppname = (uu___92_8466.ppname);
         index = uu____8467;
         sort = (uu___92_8466.sort)
       })
  
let (freshen_binder : binder -> binder) =
  fun b  ->
    let uu____8473 = b  in
    match uu____8473 with
    | (bv,aq) -> let uu____8480 = freshen_bv bv  in (uu____8480, aq)
  
let (new_univ_name :
  FStar_Range.range FStar_Pervasives_Native.option -> univ_name) =
  fun ropt  ->
    let id1 = next_id ()  in
    let uu____8493 =
      let uu____8498 =
        let uu____8499 = FStar_Util.string_of_int id1  in
        Prims.strcat FStar_Ident.reserved_prefix uu____8499  in
      (uu____8498, (range_of_ropt ropt))  in
    FStar_Ident.mk_ident uu____8493
  
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
      | uu____8573 -> false
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun fv1  ->
    fun fv2  -> FStar_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
  
let (fv_eq_lid : fv -> FStar_Ident.lident -> Prims.bool) =
  fun fv  -> fun lid  -> FStar_Ident.lid_equals (fv.fv_name).v lid 
let (set_bv_range : bv -> FStar_Range.range -> bv) =
  fun bv  ->
    fun r  ->
      let uu___93_8616 = bv  in
      let uu____8617 =
        FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r)  in
      {
        ppname = uu____8617;
        index = (uu___93_8616.index);
        sort = (uu___93_8616.sort)
      }
  
let (lid_as_fv :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> fv)
  =
  fun l  ->
    fun dd  ->
      fun dq  ->
        let uu____8637 =
          let uu____8638 = FStar_Ident.range_of_lid l  in
          withinfo l uu____8638  in
        { fv_name = uu____8637; fv_delta = dd; fv_qual = dq }
  
let (fv_to_tm : fv -> term) =
  fun fv  ->
    let uu____8644 = FStar_Ident.range_of_lid (fv.fv_name).v  in
    mk (Tm_fvar fv) FStar_Pervasives_Native.None uu____8644
  
let (fvar :
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> term)
  =
  fun l  ->
    fun dd  ->
      fun dq  -> let uu____8664 = lid_as_fv l dd dq  in fv_to_tm uu____8664
  
let (lid_of_fv : fv -> FStar_Ident.lid) = fun fv  -> (fv.fv_name).v 
let (range_of_fv : fv -> FStar_Range.range) =
  fun fv  ->
    let uu____8675 = lid_of_fv fv  in FStar_Ident.range_of_lid uu____8675
  
let (set_range_of_fv : fv -> FStar_Range.range -> fv) =
  fun fv  ->
    fun r  ->
      let uu___94_8686 = fv  in
      let uu____8687 =
        let uu___95_8688 = fv.fv_name  in
        let uu____8689 =
          let uu____8690 = lid_of_fv fv  in
          FStar_Ident.set_lid_range uu____8690 r  in
        { v = uu____8689; p = (uu___95_8688.p) }  in
      {
        fv_name = uu____8687;
        fv_delta = (uu___94_8686.fv_delta);
        fv_qual = (uu___94_8686.fv_qual)
      }
  
let (has_simple_attribute : term Prims.list -> Prims.string -> Prims.bool) =
  fun l  ->
    fun s  ->
      FStar_List.existsb
        (fun uu___89_8712  ->
           match uu___89_8712 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____8716));
               pos = uu____8717; vars = uu____8718;_} when data = s -> true
           | uu____8721 -> false) l
  
let rec (eq_pat : pat -> pat -> Prims.bool) =
  fun p1  ->
    fun p2  ->
      match ((p1.v), (p2.v)) with
      | (Pat_constant c1,Pat_constant c2) -> FStar_Const.eq_const c1 c2
      | (Pat_cons (fv1,as1),Pat_cons (fv2,as2)) ->
          let uu____8772 = fv_eq fv1 fv2  in
          if uu____8772
          then
            let uu____8774 = FStar_List.zip as1 as2  in
            FStar_All.pipe_right uu____8774
              (FStar_List.for_all
                 (fun uu____8832  ->
                    match uu____8832 with
                    | ((p11,b1),(p21,b2)) -> (b1 = b2) && (eq_pat p11 p21)))
          else false
      | (Pat_var uu____8858,Pat_var uu____8859) -> true
      | (Pat_wild uu____8860,Pat_wild uu____8861) -> true
      | (Pat_dot_term (bv1,t1),Pat_dot_term (bv2,t2)) -> true
      | (uu____8874,uu____8875) -> false
  
let (delta_constant : delta_depth) =
  Delta_constant_at_level (Prims.parse_int "0") 
let (delta_equational : delta_depth) =
  Delta_equational_at_level (Prims.parse_int "0") 
let (fvconst : FStar_Ident.lident -> fv) =
  fun l  -> lid_as_fv l delta_constant FStar_Pervasives_Native.None 
let (tconst : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____8886 =
      let uu____8893 = let uu____8894 = fvconst l  in Tm_fvar uu____8894  in
      mk uu____8893  in
    uu____8886 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tabbrev : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____8903 =
      let uu____8910 =
        let uu____8911 =
          lid_as_fv l (Delta_constant_at_level (Prims.parse_int "1"))
            FStar_Pervasives_Native.None
           in
        Tm_fvar uu____8911  in
      mk uu____8910  in
    uu____8903 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (tdataconstr : FStar_Ident.lident -> term) =
  fun l  ->
    let uu____8920 =
      lid_as_fv l delta_constant (FStar_Pervasives_Native.Some Data_ctor)  in
    fv_to_tm uu____8920
  
let (t_unit : term) = tconst FStar_Parser_Const.unit_lid 
let (t_bool : term) = tconst FStar_Parser_Const.bool_lid 
let (t_int : term) = tconst FStar_Parser_Const.int_lid 
let (t_string : term) = tconst FStar_Parser_Const.string_lid 
let (t_float : term) = tconst FStar_Parser_Const.float_lid 
let (t_char : term) = tabbrev FStar_Parser_Const.char_lid 
let (t_range : term) = tconst FStar_Parser_Const.range_lid 
let (t_term : term) = tconst FStar_Parser_Const.term_lid 
let (t_order : term) = tconst FStar_Parser_Const.order_lid 
let (t_decls : term) = tabbrev FStar_Parser_Const.decls_lid 
let (t_binder : term) = tconst FStar_Parser_Const.binder_lid 
let (t_binders : term) = tconst FStar_Parser_Const.binders_lid 
let (t_bv : term) = tconst FStar_Parser_Const.bv_lid 
let (t_fv : term) = tconst FStar_Parser_Const.fv_lid 
let (t_norm_step : term) = tconst FStar_Parser_Const.norm_step_lid 
let (t_tactic_unit : term) =
  let uu____8921 =
    let uu____8926 =
      let uu____8927 = tabbrev FStar_Parser_Const.tactic_lid  in
      mk_Tm_uinst uu____8927 [U_zero]  in
    let uu____8928 = let uu____8929 = as_arg t_unit  in [uu____8929]  in
    mk_Tm_app uu____8926 uu____8928  in
  uu____8921 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (t_tac_unit : term) =
  let uu____8956 =
    let uu____8961 =
      let uu____8962 = tabbrev FStar_Parser_Const.u_tac_lid  in
      mk_Tm_uinst uu____8962 [U_zero]  in
    let uu____8963 = let uu____8964 = as_arg t_unit  in [uu____8964]  in
    mk_Tm_app uu____8961 uu____8963  in
  uu____8956 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (t_list_of : term -> term) =
  fun t  ->
    let uu____8996 =
      let uu____9001 =
        let uu____9002 = tabbrev FStar_Parser_Const.list_lid  in
        mk_Tm_uinst uu____9002 [U_zero]  in
      let uu____9003 = let uu____9004 = as_arg t  in [uu____9004]  in
      mk_Tm_app uu____9001 uu____9003  in
    uu____8996 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_option_of : term -> term) =
  fun t  ->
    let uu____9036 =
      let uu____9041 =
        let uu____9042 = tabbrev FStar_Parser_Const.option_lid  in
        mk_Tm_uinst uu____9042 [U_zero]  in
      let uu____9043 = let uu____9044 = as_arg t  in [uu____9044]  in
      mk_Tm_app uu____9041 uu____9043  in
    uu____9036 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_tuple2_of : term -> term -> term) =
  fun t1  ->
    fun t2  ->
      let uu____9081 =
        let uu____9086 =
          let uu____9087 = tabbrev FStar_Parser_Const.lid_tuple2  in
          mk_Tm_uinst uu____9087 [U_zero; U_zero]  in
        let uu____9088 =
          let uu____9089 = as_arg t1  in
          let uu____9098 = let uu____9109 = as_arg t2  in [uu____9109]  in
          uu____9089 :: uu____9098  in
        mk_Tm_app uu____9086 uu____9088  in
      uu____9081 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (t_either_of : term -> term -> term) =
  fun t1  ->
    fun t2  ->
      let uu____9154 =
        let uu____9159 =
          let uu____9160 = tabbrev FStar_Parser_Const.either_lid  in
          mk_Tm_uinst uu____9160 [U_zero; U_zero]  in
        let uu____9161 =
          let uu____9162 = as_arg t1  in
          let uu____9171 = let uu____9182 = as_arg t2  in [uu____9182]  in
          uu____9162 :: uu____9171  in
        mk_Tm_app uu____9159 uu____9161  in
      uu____9154 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (unit_const : term) =
  mk (Tm_constant FStar_Const.Const_unit) FStar_Pervasives_Native.None
    FStar_Range.dummyRange
  