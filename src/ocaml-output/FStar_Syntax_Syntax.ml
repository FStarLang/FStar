open Prims
type 'a withinfo_t = {
  v: 'a;
  p: FStar_Range.range;}
<<<<<<< HEAD
type var = FStar_Ident.lident withinfo_t
=======
let __proj__Mkwithinfo_t__item__v projectee =
  match projectee with
  | { v = __fname__v; ty = __fname__ty; p = __fname__p;_} -> __fname__v
let __proj__Mkwithinfo_t__item__ty projectee =
  match projectee with
  | { v = __fname__v; ty = __fname__ty; p = __fname__p;_} -> __fname__ty
let __proj__Mkwithinfo_t__item__p projectee =
  match projectee with
  | { v = __fname__v; ty = __fname__ty; p = __fname__p;_} -> __fname__p
type 't var = (FStar_Ident.lident,'t) withinfo_t
>>>>>>> origin/guido_tactics
type sconst = FStar_Const.sconst
type pragma =
  | SetOptions of Prims.string
  | ResetOptions of Prims.string option
  | LightOff
let uu___is_SetOptions: pragma -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | SetOptions _0 -> true | uu____48 -> false
=======
    match projectee with | SetOptions _0 -> true | uu____96 -> false
>>>>>>> origin/guido_tactics
let __proj__SetOptions__item___0: pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0
let uu___is_ResetOptions: pragma -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | ResetOptions _0 -> true | uu____61 -> false
=======
    match projectee with | ResetOptions _0 -> true | uu____111 -> false
>>>>>>> origin/guido_tactics
let __proj__ResetOptions__item___0: pragma -> Prims.string option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0
let uu___is_LightOff: pragma -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | LightOff  -> true | uu____75 -> false
=======
    match projectee with | LightOff  -> true | uu____127 -> false
>>>>>>> origin/guido_tactics
type 'a memo = 'a option FStar_ST.ref
type version = {
  major: Prims.int;
  minor: Prims.int;}
type arg_qualifier =
  | Implicit of Prims.bool
  | Equality
let uu___is_Implicit: arg_qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Implicit _0 -> true | uu____105 -> false
=======
    match projectee with | Implicit _0 -> true | uu____142 -> false
>>>>>>> origin/guido_tactics
let __proj__Implicit__item___0: arg_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Implicit _0 -> _0
let uu___is_Equality: arg_qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Equality  -> true | uu____116 -> false
=======
    match projectee with | Equality  -> true | uu____155 -> false
>>>>>>> origin/guido_tactics
type aqual = arg_qualifier option
type universe =
  | U_zero
  | U_succ of universe
  | U_max of universe Prims.list
  | U_bvar of Prims.int
  | U_name of FStar_Ident.ident
  | U_unif of (universe option FStar_Unionfind.p_uvar* version)
  | U_unknown
let uu___is_U_zero: universe -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | U_zero  -> true | uu____146 -> false
let uu___is_U_succ: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_succ _0 -> true | uu____151 -> false
=======
    match projectee with | U_zero  -> true | uu____184 -> false
let uu___is_U_succ: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_succ _0 -> true | uu____190 -> false
>>>>>>> origin/guido_tactics
let __proj__U_succ__item___0: universe -> universe =
  fun projectee  -> match projectee with | U_succ _0 -> _0
let uu___is_U_max: universe -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | U_max _0 -> true | uu____164 -> false
=======
    match projectee with | U_max _0 -> true | uu____205 -> false
>>>>>>> origin/guido_tactics
let __proj__U_max__item___0: universe -> universe Prims.list =
  fun projectee  -> match projectee with | U_max _0 -> _0
let uu___is_U_bvar: universe -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | U_bvar _0 -> true | uu____179 -> false
=======
    match projectee with | U_bvar _0 -> true | uu____222 -> false
>>>>>>> origin/guido_tactics
let __proj__U_bvar__item___0: universe -> Prims.int =
  fun projectee  -> match projectee with | U_bvar _0 -> _0
let uu___is_U_name: universe -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | U_name _0 -> true | uu____191 -> false
=======
    match projectee with | U_name _0 -> true | uu____236 -> false
>>>>>>> origin/guido_tactics
let __proj__U_name__item___0: universe -> FStar_Ident.ident =
  fun projectee  -> match projectee with | U_name _0 -> _0
let uu___is_U_unif: universe -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | U_unif _0 -> true | uu____207 -> false
=======
    match projectee with | U_unif _0 -> true | uu____252 -> false
>>>>>>> origin/guido_tactics
let __proj__U_unif__item___0:
  universe -> (universe option FStar_Unionfind.p_uvar* version) =
  fun projectee  -> match projectee with | U_unif _0 -> _0
let uu___is_U_unknown: universe -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | U_unknown  -> true | uu____230 -> false
=======
    match projectee with | U_unknown  -> true | uu____271 -> false
>>>>>>> origin/guido_tactics
type univ_name = FStar_Ident.ident
type universe_uvar = (universe option FStar_Unionfind.p_uvar* version)
type univ_names = univ_name Prims.list
type universes = universe Prims.list
type monad_name = FStar_Ident.lident
type delta_depth =
  | Delta_constant
  | Delta_defined_at_level of Prims.int
  | Delta_equational
  | Delta_abstract of delta_depth
let uu___is_Delta_constant: delta_depth -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Delta_constant  -> true | uu____248 -> false
=======
    match projectee with | Delta_constant  -> true | uu____288 -> false
>>>>>>> origin/guido_tactics
let uu___is_Delta_defined_at_level: delta_depth -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Delta_defined_at_level _0 -> true
<<<<<<< HEAD
    | uu____253 -> false
=======
    | uu____294 -> false
>>>>>>> origin/guido_tactics
let __proj__Delta_defined_at_level__item___0: delta_depth -> Prims.int =
  fun projectee  -> match projectee with | Delta_defined_at_level _0 -> _0
let uu___is_Delta_equational: delta_depth -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Delta_equational  -> true | uu____264 -> false
let uu___is_Delta_abstract: delta_depth -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta_abstract _0 -> true | uu____269 -> false
=======
    match projectee with | Delta_equational  -> true | uu____307 -> false
let uu___is_Delta_abstract: delta_depth -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta_abstract _0 -> true | uu____313 -> false
>>>>>>> origin/guido_tactics
let __proj__Delta_abstract__item___0: delta_depth -> delta_depth =
  fun projectee  -> match projectee with | Delta_abstract _0 -> _0
type term' =
  | Tm_bvar of bv
  | Tm_name of bv
  | Tm_fvar of fv
  | Tm_uinst of ((term',term') syntax* universes)
  | Tm_constant of sconst
  | Tm_type of universe
  | Tm_abs of ((bv* aqual) Prims.list* (term',term') syntax* residual_comp
  option)
  | Tm_arrow of ((bv* aqual) Prims.list* (comp',Prims.unit) syntax)
  | Tm_refine of (bv* (term',term') syntax)
  | Tm_app of ((term',term') syntax* ((term',term') syntax* aqual)
  Prims.list)
  | Tm_match of ((term',term') syntax* (pat' withinfo_t* (term',term') syntax
  option* (term',term') syntax) Prims.list)
  | Tm_ascribed of ((term',term') syntax*
  (((term',term') syntax,(comp',Prims.unit) syntax) FStar_Util.either*
  (term',term') syntax option)* FStar_Ident.lident option)
  | Tm_let of ((Prims.bool* letbinding Prims.list)* (term',term') syntax)
<<<<<<< HEAD
  | Tm_uvar of (((term',term') syntax option FStar_Unionfind.p_uvar*
  version)* (term',term') syntax)
  | Tm_delayed of
  ((((term',term') syntax* (subst_elt Prims.list Prims.list*
      FStar_Range.range option)),Prims.unit -> (term',term') syntax)
  FStar_Util.either* (term',term') syntax memo)
=======
  | Tm_uvar of ((term',term') syntax option FStar_Unionfind.p_uvar*
  (term',term') syntax)
  | Tm_delayed of (((term',term') syntax* (subst_elt Prims.list Prims.list*
  FStar_Range.range option))* (term',term') syntax memo)
>>>>>>> origin/guido_tactics
  | Tm_meta of ((term',term') syntax* metadata)
  | Tm_unknown
and pat' =
  | Pat_constant of sconst
  | Pat_cons of (fv* (pat' withinfo_t* Prims.bool) Prims.list)
  | Pat_var of bv
  | Pat_wild of bv
  | Pat_dot_term of (bv* (term',term') syntax)
and letbinding =
  {
  lbname: (bv,fv) FStar_Util.either;
  lbunivs: univ_name Prims.list;
  lbtyp: (term',term') syntax;
  lbeff: FStar_Ident.lident;
  lbdef: (term',term') syntax;}
and comp_typ =
  {
  comp_univs: universes;
  effect_name: FStar_Ident.lident;
  result_typ: (term',term') syntax;
  effect_args: ((term',term') syntax* aqual) Prims.list;
  flags: cflags Prims.list;}
and comp' =
  | Total of ((term',term') syntax* universe option)
  | GTotal of ((term',term') syntax* universe option)
  | Comp of comp_typ
and cflags =
  | TOTAL
  | MLEFFECT
  | RETURN
  | PARTIAL_RETURN
  | SOMETRIVIAL
  | LEMMA
  | CPS
  | DECREASES of (term',term') syntax
and metadata =
  | Meta_pattern of ((term',term') syntax* aqual) Prims.list Prims.list
  | Meta_named of FStar_Ident.lident
  | Meta_labeled of (Prims.string* FStar_Range.range* Prims.bool)
  | Meta_desugared of meta_source_info
  | Meta_monadic of (monad_name* (term',term') syntax)
  | Meta_monadic_lift of (monad_name* monad_name* (term',term') syntax)
  | Meta_alien of (FStar_Dyn.dyn* Prims.string)
and meta_source_info =
  | Data_app
  | Sequence
  | Primop
  | Masked_effect
  | Meta_smt_pat
  | Mutable_alloc
  | Mutable_rval
and fv_qual =
  | Data_ctor
  | Record_projector of (FStar_Ident.lident* FStar_Ident.ident)
  | Record_ctor of (FStar_Ident.lident* FStar_Ident.ident Prims.list)
and subst_elt =
  | DB of (Prims.int* bv)
  | NM of (bv* Prims.int)
  | NT of (bv* (term',term') syntax)
  | UN of (Prims.int* universe)
  | UD of (univ_name* Prims.int)
and ('a,'b) syntax =
  {
  n: 'a;
  tk: 'b memo;
  pos: FStar_Range.range;
  vars: free_vars memo;}
and bv =
  {
  ppname: FStar_Ident.ident;
  index: Prims.int;
  sort: (term',term') syntax;}
and fv = {
  fv_name: var;
  fv_delta: delta_depth;
  fv_qual: fv_qual option;}
and free_vars =
  {
  free_names: bv FStar_Util.set;
  free_uvars:
    (((term',term') syntax option FStar_Unionfind.p_uvar* version)*
      (term',term') syntax) FStar_Util.set;
  free_univs: universe_uvar FStar_Util.set;
  free_univ_names: univ_name FStar_Util.fifo_set;}
and lcomp =
  {
  eff_name: FStar_Ident.lident;
  res_typ: (term',term') syntax;
  cflags: cflags Prims.list;
  comp: Prims.unit -> (comp',Prims.unit) syntax;}
and residual_comp =
  {
  residual_effect: FStar_Ident.lident;
  residual_typ: (term',term') syntax option;
  residual_flags: cflags Prims.list;}
let uu___is_Tm_bvar: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_bvar _0 -> true | uu____766 -> false
=======
    match projectee with | Tm_bvar _0 -> true | uu____823 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_bvar__item___0: term' -> bv =
  fun projectee  -> match projectee with | Tm_bvar _0 -> _0
let uu___is_Tm_name: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_name _0 -> true | uu____778 -> false
=======
    match projectee with | Tm_name _0 -> true | uu____837 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_name__item___0: term' -> bv =
  fun projectee  -> match projectee with | Tm_name _0 -> _0
let uu___is_Tm_fvar: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_fvar _0 -> true | uu____790 -> false
=======
    match projectee with | Tm_fvar _0 -> true | uu____851 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_fvar__item___0: term' -> fv =
  fun projectee  -> match projectee with | Tm_fvar _0 -> _0
let uu___is_Tm_uinst: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_uinst _0 -> true | uu____806 -> false
=======
    match projectee with | Tm_uinst _0 -> true | uu____869 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_uinst__item___0: term' -> ((term',term') syntax* universes) =
  fun projectee  -> match projectee with | Tm_uinst _0 -> _0
let uu___is_Tm_constant: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_constant _0 -> true | uu____830 -> false
=======
    match projectee with | Tm_constant _0 -> true | uu____895 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_constant__item___0: term' -> sconst =
  fun projectee  -> match projectee with | Tm_constant _0 -> _0
let uu___is_Tm_type: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_type _0 -> true | uu____842 -> false
=======
    match projectee with | Tm_type _0 -> true | uu____909 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_type__item___0: term' -> universe =
  fun projectee  -> match projectee with | Tm_type _0 -> _0
let uu___is_Tm_abs: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_abs _0 -> true | uu____868 -> false
=======
    match projectee with | Tm_abs _0 -> true | uu____932 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_abs__item___0:
  term' ->
    ((bv* aqual) Prims.list* (term',term') syntax* residual_comp option)
  = fun projectee  -> match projectee with | Tm_abs _0 -> _0
let uu___is_Tm_arrow: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_arrow _0 -> true | uu____929 -> false
=======
    match projectee with | Tm_arrow _0 -> true | uu____980 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_arrow__item___0:
  term' -> ((bv* aqual) Prims.list* (comp',Prims.unit) syntax) =
  fun projectee  -> match projectee with | Tm_arrow _0 -> _0
let uu___is_Tm_refine: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_refine _0 -> true | uu____966 -> false
=======
    match projectee with | Tm_refine _0 -> true | uu____1019 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_refine__item___0: term' -> (bv* (term',term') syntax) =
  fun projectee  -> match projectee with | Tm_refine _0 -> _0
let uu___is_Tm_app: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_app _0 -> true | uu____999 -> false
=======
    match projectee with | Tm_app _0 -> true | uu____1054 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_app__item___0:
  term' -> ((term',term') syntax* ((term',term') syntax* aqual) Prims.list) =
  fun projectee  -> match projectee with | Tm_app _0 -> _0
let uu___is_Tm_match: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_match _0 -> true | uu____1052 -> false
=======
    match projectee with | Tm_match _0 -> true | uu____1110 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_match__item___0:
  term' ->
    ((term',term') syntax* (pat' withinfo_t* (term',term') syntax option*
      (term',term') syntax) Prims.list)
  = fun projectee  -> match projectee with | Tm_match _0 -> _0
let uu___is_Tm_ascribed: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_ascribed _0 -> true | uu____1123 -> false
=======
    match projectee with | Tm_ascribed _0 -> true | uu____1186 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_ascribed__item___0:
  term' ->
    ((term',term') syntax* (((term',term') syntax,(comp',Prims.unit) syntax)
      FStar_Util.either* (term',term') syntax option)* FStar_Ident.lident
      option)
  = fun projectee  -> match projectee with | Tm_ascribed _0 -> _0
let uu___is_Tm_let: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_let _0 -> true | uu____1193 -> false
=======
    match projectee with | Tm_let _0 -> true | uu____1258 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_let__item___0:
  term' -> ((Prims.bool* letbinding Prims.list)* (term',term') syntax) =
  fun projectee  -> match projectee with | Tm_let _0 -> _0
let uu___is_Tm_uvar: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_uvar _0 -> true | uu____1236 -> false
=======
    match projectee with | Tm_uvar _0 -> true | uu____1301 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_uvar__item___0:
  term' ->
    (((term',term') syntax option FStar_Unionfind.p_uvar* version)*
      (term',term') syntax)
  = fun projectee  -> match projectee with | Tm_uvar _0 -> _0
let uu___is_Tm_delayed: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_delayed _0 -> true | uu____1298 -> false
=======
    match projectee with | Tm_delayed _0 -> true | uu____1353 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_delayed__item___0:
  term' ->
    (((term',term') syntax* (subst_elt Prims.list Prims.list*
      FStar_Range.range option))* (term',term') syntax memo)
  = fun projectee  -> match projectee with | Tm_delayed _0 -> _0
let uu___is_Tm_meta: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_meta _0 -> true | uu____1374 -> false
=======
    match projectee with | Tm_meta _0 -> true | uu____1413 -> false
>>>>>>> origin/guido_tactics
let __proj__Tm_meta__item___0: term' -> ((term',term') syntax* metadata) =
  fun projectee  -> match projectee with | Tm_meta _0 -> _0
let uu___is_Tm_unknown: term' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Tm_unknown  -> true | uu____1397 -> false
let uu___is_Pat_constant: pat' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_constant _0 -> true | uu____1402 -> false
=======
    match projectee with | Tm_unknown  -> true | uu____1438 -> false
let uu___is_Pat_constant: pat' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_constant _0 -> true | uu____1444 -> false
>>>>>>> origin/guido_tactics
let __proj__Pat_constant__item___0: pat' -> sconst =
  fun projectee  -> match projectee with | Pat_constant _0 -> _0
let uu___is_Pat_cons: pat' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Pat_cons _0 -> true | uu____1420 -> false
=======
    match projectee with | Pat_cons _0 -> true | uu____1465 -> false
>>>>>>> origin/guido_tactics
let __proj__Pat_cons__item___0:
  pat' -> (fv* (pat' withinfo_t* Prims.bool) Prims.list) =
  fun projectee  -> match projectee with | Pat_cons _0 -> _0
let uu___is_Pat_var: pat' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Pat_var _0 -> true | uu____1450 -> false
=======
    match projectee with | Pat_var _0 -> true | uu____1500 -> false
>>>>>>> origin/guido_tactics
let __proj__Pat_var__item___0: pat' -> bv =
  fun projectee  -> match projectee with | Pat_var _0 -> _0
let uu___is_Pat_wild: pat' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Pat_wild _0 -> true | uu____1462 -> false
=======
    match projectee with | Pat_wild _0 -> true | uu____1514 -> false
>>>>>>> origin/guido_tactics
let __proj__Pat_wild__item___0: pat' -> bv =
  fun projectee  -> match projectee with | Pat_wild _0 -> _0
let uu___is_Pat_dot_term: pat' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Pat_dot_term _0 -> true | uu____1478 -> false
=======
    match projectee with | Pat_dot_term _0 -> true | uu____1532 -> false
>>>>>>> origin/guido_tactics
let __proj__Pat_dot_term__item___0: pat' -> (bv* (term',term') syntax) =
  fun projectee  -> match projectee with | Pat_dot_term _0 -> _0
let __proj__Mkletbinding__item__lbname:
  letbinding -> (bv,fv) FStar_Util.either =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef;_} -> __fname__lbname
let __proj__Mkletbinding__item__lbunivs: letbinding -> univ_name Prims.list =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef;_} -> __fname__lbunivs
let __proj__Mkletbinding__item__lbtyp: letbinding -> (term',term') syntax =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef;_} -> __fname__lbtyp
let __proj__Mkletbinding__item__lbeff: letbinding -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef;_} -> __fname__lbeff
let __proj__Mkletbinding__item__lbdef: letbinding -> (term',term') syntax =
  fun projectee  ->
    match projectee with
    | { lbname = __fname__lbname; lbunivs = __fname__lbunivs;
        lbtyp = __fname__lbtyp; lbeff = __fname__lbeff;
        lbdef = __fname__lbdef;_} -> __fname__lbdef
let __proj__Mkcomp_typ__item__comp_univs: comp_typ -> universes =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__comp_univs
let __proj__Mkcomp_typ__item__effect_name: comp_typ -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_name
let __proj__Mkcomp_typ__item__result_typ: comp_typ -> (term',term') syntax =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__result_typ
let __proj__Mkcomp_typ__item__effect_args:
  comp_typ -> ((term',term') syntax* aqual) Prims.list =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_args
let __proj__Mkcomp_typ__item__flags: comp_typ -> cflags Prims.list =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__flags
let uu___is_Total: comp' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Total _0 -> true | uu____1577 -> false
=======
    match projectee with | Total _0 -> true | uu____1758 -> false
>>>>>>> origin/guido_tactics
let __proj__Total__item___0: comp' -> ((term',term') syntax* universe option)
  = fun projectee  -> match projectee with | Total _0 -> _0
let uu___is_GTotal: comp' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | GTotal _0 -> true | uu____1609 -> false
=======
    match projectee with | GTotal _0 -> true | uu____1792 -> false
>>>>>>> origin/guido_tactics
let __proj__GTotal__item___0:
  comp' -> ((term',term') syntax* universe option) =
  fun projectee  -> match projectee with | GTotal _0 -> _0
let uu___is_Comp: comp' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Comp _0 -> true | uu____1636 -> false
=======
    match projectee with | Comp _0 -> true | uu____1821 -> false
>>>>>>> origin/guido_tactics
let __proj__Comp__item___0: comp' -> comp_typ =
  fun projectee  -> match projectee with | Comp _0 -> _0
let uu___is_TOTAL: cflags -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | TOTAL  -> true | uu____1647 -> false
let uu___is_MLEFFECT: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1651 -> false
let uu___is_RETURN: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1655 -> false
let uu___is_PARTIAL_RETURN: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1659 -> false
let uu___is_SOMETRIVIAL: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1663 -> false
let uu___is_LEMMA: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1667 -> false
let uu___is_CPS: cflags -> Prims.bool =
  fun projectee  -> match projectee with | CPS  -> true | uu____1671 -> false
let uu___is_DECREASES: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1678 -> false
=======
    match projectee with | TOTAL  -> true | uu____1834 -> false
let uu___is_MLEFFECT: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1839 -> false
let uu___is_RETURN: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1844 -> false
let uu___is_PARTIAL_RETURN: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1849 -> false
let uu___is_SOMETRIVIAL: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1854 -> false
let uu___is_LEMMA: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1859 -> false
let uu___is_CPS: cflags -> Prims.bool =
  fun projectee  -> match projectee with | CPS  -> true | uu____1864 -> false
let uu___is_DECREASES: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1872 -> false
>>>>>>> origin/guido_tactics
let __proj__DECREASES__item___0: cflags -> (term',term') syntax =
  fun projectee  -> match projectee with | DECREASES _0 -> _0
let uu___is_Meta_pattern: metadata -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Meta_pattern _0 -> true | uu____1702 -> false
=======
    match projectee with | Meta_pattern _0 -> true | uu____1898 -> false
>>>>>>> origin/guido_tactics
let __proj__Meta_pattern__item___0:
  metadata -> ((term',term') syntax* aqual) Prims.list Prims.list =
  fun projectee  -> match projectee with | Meta_pattern _0 -> _0
let uu___is_Meta_named: metadata -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Meta_named _0 -> true | uu____1732 -> false
=======
    match projectee with | Meta_named _0 -> true | uu____1930 -> false
>>>>>>> origin/guido_tactics
let __proj__Meta_named__item___0: metadata -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Meta_named _0 -> _0
let uu___is_Meta_labeled: metadata -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Meta_labeled _0 -> true | uu____1747 -> false
=======
    match projectee with | Meta_labeled _0 -> true | uu____1947 -> false
>>>>>>> origin/guido_tactics
let __proj__Meta_labeled__item___0:
  metadata -> (Prims.string* FStar_Range.range* Prims.bool) =
  fun projectee  -> match projectee with | Meta_labeled _0 -> _0
let uu___is_Meta_desugared: metadata -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Meta_desugared _0 -> true | uu____1768 -> false
=======
    match projectee with | Meta_desugared _0 -> true | uu____1970 -> false
>>>>>>> origin/guido_tactics
let __proj__Meta_desugared__item___0: metadata -> meta_source_info =
  fun projectee  -> match projectee with | Meta_desugared _0 -> _0
let uu___is_Meta_monadic: metadata -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Meta_monadic _0 -> true | uu____1784 -> false
=======
    match projectee with | Meta_monadic _0 -> true | uu____1988 -> false
>>>>>>> origin/guido_tactics
let __proj__Meta_monadic__item___0:
  metadata -> (monad_name* (term',term') syntax) =
  fun projectee  -> match projectee with | Meta_monadic _0 -> _0
let uu___is_Meta_monadic_lift: metadata -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Meta_monadic_lift _0 -> true | uu____1813 -> false
let __proj__Meta_monadic_lift__item___0:
  metadata -> (monad_name* monad_name* (term',term') syntax) =
  fun projectee  -> match projectee with | Meta_monadic_lift _0 -> _0
let uu___is_Data_app: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Data_app  -> true | uu____1839 -> false
let uu___is_Sequence: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Sequence  -> true | uu____1843 -> false
let uu___is_Primop: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Primop  -> true | uu____1847 -> false
let uu___is_Masked_effect: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Masked_effect  -> true | uu____1851 -> false
let uu___is_Meta_smt_pat: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_smt_pat  -> true | uu____1855 -> false
let uu___is_Mutable_alloc: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable_alloc  -> true | uu____1859 -> false
let uu___is_Mutable_rval: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable_rval  -> true | uu____1863 -> false
let uu___is_Data_ctor: fv_qual -> Prims.bool =
  fun projectee  ->
    match projectee with | Data_ctor  -> true | uu____1867 -> false
let uu___is_Record_projector: fv_qual -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_projector _0 -> true | uu____1874 -> false
=======
    match projectee with | Meta_monadic_lift _0 -> true | uu____2019 -> false
let __proj__Meta_monadic_lift__item___0:
  metadata -> (monad_name* monad_name* (term',term') syntax) =
  fun projectee  -> match projectee with | Meta_monadic_lift _0 -> _0
let uu___is_Meta_alien: metadata -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_alien _0 -> true | uu____2050 -> false
let __proj__Meta_alien__item___0: metadata -> (FStar_Dyn.dyn* Prims.string) =
  fun projectee  -> match projectee with | Meta_alien _0 -> _0
let uu___is_Data_app: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Data_app  -> true | uu____2069 -> false
let uu___is_Sequence: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Sequence  -> true | uu____2074 -> false
let uu___is_Primop: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Primop  -> true | uu____2079 -> false
let uu___is_Masked_effect: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Masked_effect  -> true | uu____2084 -> false
let uu___is_Meta_smt_pat: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_smt_pat  -> true | uu____2089 -> false
let uu___is_Mutable_alloc: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable_alloc  -> true | uu____2094 -> false
let uu___is_Mutable_rval: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable_rval  -> true | uu____2099 -> false
let uu___is_Data_ctor: fv_qual -> Prims.bool =
  fun projectee  ->
    match projectee with | Data_ctor  -> true | uu____2104 -> false
let uu___is_Record_projector: fv_qual -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_projector _0 -> true | uu____2112 -> false
>>>>>>> origin/guido_tactics
let __proj__Record_projector__item___0:
  fv_qual -> (FStar_Ident.lident* FStar_Ident.ident) =
  fun projectee  -> match projectee with | Record_projector _0 -> _0
let uu___is_Record_ctor: fv_qual -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Record_ctor _0 -> true | uu____1895 -> false
=======
    match projectee with | Record_ctor _0 -> true | uu____2135 -> false
>>>>>>> origin/guido_tactics
let __proj__Record_ctor__item___0:
  fv_qual -> (FStar_Ident.lident* FStar_Ident.ident Prims.list) =
  fun projectee  -> match projectee with | Record_ctor _0 -> _0
let uu___is_DB: subst_elt -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | DB _0 -> true | uu____1918 -> false
=======
    match projectee with | DB _0 -> true | uu____2160 -> false
>>>>>>> origin/guido_tactics
let __proj__DB__item___0: subst_elt -> (Prims.int* bv) =
  fun projectee  -> match projectee with | DB _0 -> _0
let uu___is_NM: subst_elt -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | NM _0 -> true | uu____1938 -> false
=======
    match projectee with | NM _0 -> true | uu____2182 -> false
>>>>>>> origin/guido_tactics
let __proj__NM__item___0: subst_elt -> (bv* Prims.int) =
  fun projectee  -> match projectee with | NM _0 -> _0
let uu___is_NT: subst_elt -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | NT _0 -> true | uu____1960 -> false
=======
    match projectee with | NT _0 -> true | uu____2206 -> false
>>>>>>> origin/guido_tactics
let __proj__NT__item___0: subst_elt -> (bv* (term',term') syntax) =
  fun projectee  -> match projectee with | NT _0 -> _0
let uu___is_UN: subst_elt -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | UN _0 -> true | uu____1986 -> false
=======
    match projectee with | UN _0 -> true | uu____2234 -> false
>>>>>>> origin/guido_tactics
let __proj__UN__item___0: subst_elt -> (Prims.int* universe) =
  fun projectee  -> match projectee with | UN _0 -> _0
let uu___is_UD: subst_elt -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | UD _0 -> true | uu____2006 -> false
let __proj__UD__item___0: subst_elt -> (univ_name* Prims.int) =
  fun projectee  -> match projectee with | UD _0 -> _0
type pat = pat' withinfo_t
=======
    match projectee with | UD _0 -> true | uu____2256 -> false
let __proj__UD__item___0: subst_elt -> (univ_name* Prims.int) =
  fun projectee  -> match projectee with | UD _0 -> _0
let __proj__Mksyntax__item__n projectee =
  match projectee with
  | { n = __fname__n; tk = __fname__tk; pos = __fname__pos;
      vars = __fname__vars;_} -> __fname__n
let __proj__Mksyntax__item__tk projectee =
  match projectee with
  | { n = __fname__n; tk = __fname__tk; pos = __fname__pos;
      vars = __fname__vars;_} -> __fname__tk
let __proj__Mksyntax__item__pos projectee =
  match projectee with
  | { n = __fname__n; tk = __fname__tk; pos = __fname__pos;
      vars = __fname__vars;_} -> __fname__pos
let __proj__Mksyntax__item__vars projectee =
  match projectee with
  | { n = __fname__n; tk = __fname__tk; pos = __fname__pos;
      vars = __fname__vars;_} -> __fname__vars
let __proj__Mkbv__item__ppname: bv -> FStar_Ident.ident =
  fun projectee  ->
    match projectee with
    | { ppname = __fname__ppname; index = __fname__index;
        sort = __fname__sort;_} -> __fname__ppname
let __proj__Mkbv__item__index: bv -> Prims.int =
  fun projectee  ->
    match projectee with
    | { ppname = __fname__ppname; index = __fname__index;
        sort = __fname__sort;_} -> __fname__index
let __proj__Mkbv__item__sort: bv -> (term',term') syntax =
  fun projectee  ->
    match projectee with
    | { ppname = __fname__ppname; index = __fname__index;
        sort = __fname__sort;_} -> __fname__sort
let __proj__Mkfv__item__fv_name: fv -> (term',term') syntax var =
  fun projectee  ->
    match projectee with
    | { fv_name = __fname__fv_name; fv_delta = __fname__fv_delta;
        fv_qual = __fname__fv_qual;_} -> __fname__fv_name
let __proj__Mkfv__item__fv_delta: fv -> delta_depth =
  fun projectee  ->
    match projectee with
    | { fv_name = __fname__fv_name; fv_delta = __fname__fv_delta;
        fv_qual = __fname__fv_qual;_} -> __fname__fv_delta
let __proj__Mkfv__item__fv_qual: fv -> fv_qual option =
  fun projectee  ->
    match projectee with
    | { fv_name = __fname__fv_name; fv_delta = __fname__fv_delta;
        fv_qual = __fname__fv_qual;_} -> __fname__fv_qual
let __proj__Mkfree_vars__item__free_names: free_vars -> bv FStar_Util.set =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} -> __fname__free_names
let __proj__Mkfree_vars__item__free_uvars:
  free_vars ->
    ((term',term') syntax option FStar_Unionfind.p_uvar* (term',term')
      syntax) FStar_Util.set
  =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} -> __fname__free_uvars
let __proj__Mkfree_vars__item__free_univs:
  free_vars -> universe_uvar FStar_Util.set =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} -> __fname__free_univs
let __proj__Mkfree_vars__item__free_univ_names:
  free_vars -> univ_name FStar_Util.fifo_set =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;_} ->
        __fname__free_univ_names
let __proj__Mklcomp__item__eff_name: lcomp -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp = __fname__comp;_} ->
        __fname__eff_name
let __proj__Mklcomp__item__res_typ: lcomp -> (term',term') syntax =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp = __fname__comp;_} -> __fname__res_typ
let __proj__Mklcomp__item__cflags: lcomp -> cflags Prims.list =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp = __fname__comp;_} -> __fname__cflags
let __proj__Mklcomp__item__comp:
  lcomp -> Prims.unit -> (comp',Prims.unit) syntax =
  fun projectee  ->
    match projectee with
    | { eff_name = __fname__eff_name; res_typ = __fname__res_typ;
        cflags = __fname__cflags; comp = __fname__comp;_} -> __fname__comp
let __proj__Mkresidual_comp__item__residual_effect:
  residual_comp -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} ->
        __fname__residual_effect
let __proj__Mkresidual_comp__item__residual_typ:
  residual_comp -> (term',term') syntax option =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} -> __fname__residual_typ
let __proj__Mkresidual_comp__item__residual_flags:
  residual_comp -> cflags Prims.list =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} ->
        __fname__residual_flags
type pat = (pat',term') withinfo_t
>>>>>>> origin/guido_tactics
type term = (term',term') syntax
type branch =
  (pat' withinfo_t* (term',term') syntax option* (term',term') syntax)
type comp = (comp',Prims.unit) syntax
type ascription =
  (((term',term') syntax,(comp',Prims.unit) syntax) FStar_Util.either*
    (term',term') syntax option)
type typ = (term',term') syntax
type arg = ((term',term') syntax* aqual)
type args = ((term',term') syntax* aqual) Prims.list
type binder = (bv* aqual)
type binders = (bv* aqual) Prims.list
type uvar = ((term',term') syntax option FStar_Unionfind.p_uvar* version)
type lbname = (bv,fv) FStar_Util.either
type letbindings = (Prims.bool* letbinding Prims.list)
type subst_ts = (subst_elt Prims.list Prims.list* FStar_Range.range option)
type freenames = bv FStar_Util.set
type uvars =
<<<<<<< HEAD
  (((term',term') syntax option FStar_Unionfind.p_uvar* version)*
    (term',term') syntax) FStar_Util.set
type residual_comp = (FStar_Ident.lident* cflags Prims.list)
=======
  ((term',term') syntax option FStar_Unionfind.p_uvar* (term',term') syntax)
    FStar_Util.set
>>>>>>> origin/guido_tactics
type tscheme = (univ_name Prims.list* typ)
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
  | Projector of (FStar_Ident.lident* FStar_Ident.ident)
  | RecordType of (FStar_Ident.ident Prims.list* FStar_Ident.ident
  Prims.list)
  | RecordConstructor of (FStar_Ident.ident Prims.list* FStar_Ident.ident
  Prims.list)
  | Action of FStar_Ident.lident
  | ExceptionConstructor
  | HasMaskedEffect
  | Effect
  | OnlyName
let uu___is_Assumption: qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Assumption  -> true | uu____2312 -> false
let uu___is_New: qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____2316 -> false
let uu___is_Private: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____2320 -> false
=======
    match projectee with | Assumption  -> true | uu____2775 -> false
let uu___is_New: qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____2780 -> false
let uu___is_Private: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____2785 -> false
>>>>>>> origin/guido_tactics
let uu___is_Unfold_for_unification_and_vcgen: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
<<<<<<< HEAD
    | uu____2324 -> false
let uu___is_Visible_default: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____2328 -> false
let uu___is_Irreducible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____2332 -> false
let uu___is_Abstract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____2336 -> false
=======
    | uu____2790 -> false
let uu___is_Visible_default: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____2795 -> false
let uu___is_Irreducible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____2800 -> false
let uu___is_Abstract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____2805 -> false
>>>>>>> origin/guido_tactics
let uu___is_Inline_for_extraction: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
<<<<<<< HEAD
    | uu____2340 -> false
let uu___is_NoExtract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____2344 -> false
let uu___is_Noeq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____2348 -> false
let uu___is_Unopteq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____2352 -> false
let uu___is_TotalEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____2356 -> false
let uu___is_Logic: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____2360 -> false
let uu___is_Reifiable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____2364 -> false
let uu___is_Reflectable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____2369 -> false
=======
    | uu____2810 -> false
let uu___is_NoExtract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____2815 -> false
let uu___is_Noeq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____2820 -> false
let uu___is_Unopteq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____2825 -> false
let uu___is_TotalEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____2830 -> false
let uu___is_Logic: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____2835 -> false
let uu___is_Reifiable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____2840 -> false
let uu___is_Reflectable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____2846 -> false
>>>>>>> origin/guido_tactics
let __proj__Reflectable__item___0: qualifier -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Reflectable _0 -> _0
let uu___is_Discriminator: qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Discriminator _0 -> true | uu____2381 -> false
=======
    match projectee with | Discriminator _0 -> true | uu____2860 -> false
>>>>>>> origin/guido_tactics
let __proj__Discriminator__item___0: qualifier -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Discriminator _0 -> _0
let uu___is_Projector: qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Projector _0 -> true | uu____2395 -> false
=======
    match projectee with | Projector _0 -> true | uu____2876 -> false
>>>>>>> origin/guido_tactics
let __proj__Projector__item___0:
  qualifier -> (FStar_Ident.lident* FStar_Ident.ident) =
  fun projectee  -> match projectee with | Projector _0 -> _0
let uu___is_RecordType: qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | RecordType _0 -> true | uu____2417 -> false
=======
    match projectee with | RecordType _0 -> true | uu____2900 -> false
>>>>>>> origin/guido_tactics
let __proj__RecordType__item___0:
  qualifier -> (FStar_Ident.ident Prims.list* FStar_Ident.ident Prims.list) =
  fun projectee  -> match projectee with | RecordType _0 -> _0
let uu___is_RecordConstructor: qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | RecordConstructor _0 -> true | uu____2445 -> false
=======
    match projectee with | RecordConstructor _0 -> true | uu____2930 -> false
>>>>>>> origin/guido_tactics
let __proj__RecordConstructor__item___0:
  qualifier -> (FStar_Ident.ident Prims.list* FStar_Ident.ident Prims.list) =
  fun projectee  -> match projectee with | RecordConstructor _0 -> _0
let uu___is_Action: qualifier -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Action _0 -> true | uu____2469 -> false
=======
    match projectee with | Action _0 -> true | uu____2956 -> false
>>>>>>> origin/guido_tactics
let __proj__Action__item___0: qualifier -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Action _0 -> _0
let uu___is_ExceptionConstructor: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExceptionConstructor  -> true
<<<<<<< HEAD
    | uu____2480 -> false
let uu___is_HasMaskedEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | HasMaskedEffect  -> true | uu____2484 -> false
let uu___is_Effect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect  -> true | uu____2488 -> false
let uu___is_OnlyName: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | OnlyName  -> true | uu____2492 -> false
=======
    | uu____2969 -> false
let uu___is_HasMaskedEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | HasMaskedEffect  -> true | uu____2974 -> false
let uu___is_Effect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect  -> true | uu____2979 -> false
let uu___is_OnlyName: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | OnlyName  -> true | uu____2984 -> false
>>>>>>> origin/guido_tactics
type attribute = term
type tycon = (FStar_Ident.lident* binders* typ)
type monad_abbrev = {
  mabbrev: FStar_Ident.lident;
  parms: binders;
  def: typ;}
let __proj__Mkmonad_abbrev__item__mabbrev: monad_abbrev -> FStar_Ident.lident
  =
  fun projectee  ->
    match projectee with
    | { mabbrev = __fname__mabbrev; parms = __fname__parms;
        def = __fname__def;_} -> __fname__mabbrev
let __proj__Mkmonad_abbrev__item__parms: monad_abbrev -> binders =
  fun projectee  ->
    match projectee with
    | { mabbrev = __fname__mabbrev; parms = __fname__parms;
        def = __fname__def;_} -> __fname__parms
let __proj__Mkmonad_abbrev__item__def: monad_abbrev -> typ =
  fun projectee  ->
    match projectee with
    | { mabbrev = __fname__mabbrev; parms = __fname__parms;
        def = __fname__def;_} -> __fname__def
type sub_eff =
  {
  source: FStar_Ident.lident;
  target: FStar_Ident.lident;
  lift_wp: tscheme option;
  lift: tscheme option;}
let __proj__Mksub_eff__item__source: sub_eff -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} ->
        __fname__source
let __proj__Mksub_eff__item__target: sub_eff -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} ->
        __fname__target
let __proj__Mksub_eff__item__lift_wp: sub_eff -> tscheme option =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} ->
        __fname__lift_wp
let __proj__Mksub_eff__item__lift: sub_eff -> tscheme option =
  fun projectee  ->
    match projectee with
    | { source = __fname__source; target = __fname__target;
        lift_wp = __fname__lift_wp; lift = __fname__lift;_} -> __fname__lift
type action =
  {
  action_name: FStar_Ident.lident;
  action_unqualified_name: FStar_Ident.ident;
  action_univs: univ_names;
  action_params: binders;
  action_defn: term;
  action_typ: typ;}
let __proj__Mkaction__item__action_name: action -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_name
let __proj__Mkaction__item__action_unqualified_name:
  action -> FStar_Ident.ident =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} ->
        __fname__action_unqualified_name
let __proj__Mkaction__item__action_univs: action -> univ_names =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_univs
let __proj__Mkaction__item__action_params: action -> binders =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_params
let __proj__Mkaction__item__action_defn: action -> term =
  fun projectee  ->
    match projectee with
    | { action_name = __fname__action_name;
        action_unqualified_name = __fname__action_unqualified_name;
        action_univs = __fname__action_univs;
        action_params = __fname__action_params;
        action_defn = __fname__action_defn;
        action_typ = __fname__action_typ;_} -> __fname__action_defn
let __proj__Mkaction__item__action_typ: action -> typ =
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
  cattributes: cflags Prims.list;
  mname: FStar_Ident.lident;
  univs: univ_names;
  binders: binders;
  signature: term;
  ret_wp: tscheme;
  bind_wp: tscheme;
  if_then_else: tscheme;
  ite_wp: tscheme;
  stronger: tscheme;
  close_wp: tscheme;
  assert_p: tscheme;
  assume_p: tscheme;
  null_wp: tscheme;
  trivial: tscheme;
  repr: term;
  return_repr: tscheme;
  bind_repr: tscheme;
  actions: action Prims.list;}
let __proj__Mkeff_decl__item__cattributes: eff_decl -> cflags Prims.list =
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
        actions = __fname__actions;_} -> __fname__cattributes
let __proj__Mkeff_decl__item__mname: eff_decl -> FStar_Ident.lident =
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
        actions = __fname__actions;_} -> __fname__mname
let __proj__Mkeff_decl__item__univs: eff_decl -> univ_names =
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
        actions = __fname__actions;_} -> __fname__univs
let __proj__Mkeff_decl__item__binders: eff_decl -> binders =
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
        actions = __fname__actions;_} -> __fname__binders
let __proj__Mkeff_decl__item__signature: eff_decl -> term =
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
        actions = __fname__actions;_} -> __fname__signature
let __proj__Mkeff_decl__item__ret_wp: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__ret_wp
let __proj__Mkeff_decl__item__bind_wp: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__bind_wp
let __proj__Mkeff_decl__item__if_then_else: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__if_then_else
let __proj__Mkeff_decl__item__ite_wp: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__ite_wp
let __proj__Mkeff_decl__item__stronger: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__stronger
let __proj__Mkeff_decl__item__close_wp: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__close_wp
let __proj__Mkeff_decl__item__assert_p: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__assert_p
let __proj__Mkeff_decl__item__assume_p: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__assume_p
let __proj__Mkeff_decl__item__null_wp: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__null_wp
let __proj__Mkeff_decl__item__trivial: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__trivial
let __proj__Mkeff_decl__item__repr: eff_decl -> term =
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
        actions = __fname__actions;_} -> __fname__repr
let __proj__Mkeff_decl__item__return_repr: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__return_repr
let __proj__Mkeff_decl__item__bind_repr: eff_decl -> tscheme =
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
        actions = __fname__actions;_} -> __fname__bind_repr
let __proj__Mkeff_decl__item__actions: eff_decl -> action Prims.list =
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
        actions = __fname__actions;_} -> __fname__actions
type sig_metadata =
  {
  sigmeta_active: Prims.bool;
  sigmeta_fact_db_ids: Prims.string Prims.list;}
let __proj__Mksig_metadata__item__sigmeta_active: sig_metadata -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { sigmeta_active = __fname__sigmeta_active;
        sigmeta_fact_db_ids = __fname__sigmeta_fact_db_ids;_} ->
        __fname__sigmeta_active
let __proj__Mksig_metadata__item__sigmeta_fact_db_ids:
  sig_metadata -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { sigmeta_active = __fname__sigmeta_active;
        sigmeta_fact_db_ids = __fname__sigmeta_fact_db_ids;_} ->
        __fname__sigmeta_fact_db_ids
type sigelt' =
  | Sig_inductive_typ of (FStar_Ident.lident* univ_names* binders* typ*
  FStar_Ident.lident Prims.list* FStar_Ident.lident Prims.list)
  | Sig_bundle of (sigelt Prims.list* FStar_Ident.lident Prims.list)
  | Sig_datacon of (FStar_Ident.lident* univ_names* typ* FStar_Ident.lident*
  Prims.int* FStar_Ident.lident Prims.list)
  | Sig_declare_typ of (FStar_Ident.lident* univ_names* typ)
  | Sig_let of (letbindings* FStar_Ident.lident Prims.list* attribute
  Prims.list)
  | Sig_main of term
  | Sig_assume of (FStar_Ident.lident* univ_names* formula)
  | Sig_new_effect of eff_decl
  | Sig_new_effect_for_free of eff_decl
  | Sig_sub_effect of sub_eff
  | Sig_effect_abbrev of (FStar_Ident.lident* univ_names* binders* comp*
  cflags Prims.list)
  | Sig_pragma of pragma
and sigelt =
  {
  sigel: sigelt';
  sigrng: FStar_Range.range;
  sigquals: qualifier Prims.list;
  sigmeta: sig_metadata;}
let uu___is_Sig_inductive_typ: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_inductive_typ _0 -> true | uu____2896 -> false
=======
    match projectee with | Sig_inductive_typ _0 -> true | uu____3862 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_inductive_typ__item___0:
  sigelt' ->
    (FStar_Ident.lident* univ_names* binders* typ* FStar_Ident.lident
      Prims.list* FStar_Ident.lident Prims.list)
  = fun projectee  -> match projectee with | Sig_inductive_typ _0 -> _0
let uu___is_Sig_bundle: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_bundle _0 -> true | uu____2936 -> false
=======
    match projectee with | Sig_bundle _0 -> true | uu____3904 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_bundle__item___0:
  sigelt' -> (sigelt Prims.list* FStar_Ident.lident Prims.list) =
  fun projectee  -> match projectee with | Sig_bundle _0 -> _0
let uu___is_Sig_datacon: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_datacon _0 -> true | uu____2967 -> false
=======
    match projectee with | Sig_datacon _0 -> true | uu____3937 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_datacon__item___0:
  sigelt' ->
    (FStar_Ident.lident* univ_names* typ* FStar_Ident.lident* Prims.int*
      FStar_Ident.lident Prims.list)
  = fun projectee  -> match projectee with | Sig_datacon _0 -> _0
let uu___is_Sig_declare_typ: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_declare_typ _0 -> true | uu____3003 -> false
=======
    match projectee with | Sig_declare_typ _0 -> true | uu____3975 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_declare_typ__item___0:
  sigelt' -> (FStar_Ident.lident* univ_names* typ) =
  fun projectee  -> match projectee with | Sig_declare_typ _0 -> _0
let uu___is_Sig_let: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_let _0 -> true | uu____3029 -> false
=======
    match projectee with | Sig_let _0 -> true | uu____4003 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_let__item___0:
  sigelt' ->
    (letbindings* FStar_Ident.lident Prims.list* attribute Prims.list)
  = fun projectee  -> match projectee with | Sig_let _0 -> _0
let uu___is_Sig_main: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_main _0 -> true | uu____3056 -> false
=======
    match projectee with | Sig_main _0 -> true | uu____4032 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_main__item___0: sigelt' -> term =
  fun projectee  -> match projectee with | Sig_main _0 -> _0
let uu___is_Sig_assume: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_assume _0 -> true | uu____3071 -> false
let __proj__Sig_assume__item___0:
  sigelt' -> (FStar_Ident.lident* univ_names* formula) =
  fun projectee  -> match projectee with | Sig_assume _0 -> _0
let uu___is_Sig_new_effect: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_new_effect _0 -> true | uu____3092 -> false
=======
    match projectee with | Sig_assume _0 -> true | uu____4048 -> false
let __proj__Sig_assume__item___0: sigelt' -> (FStar_Ident.lident* formula) =
  fun projectee  -> match projectee with | Sig_assume _0 -> _0
let uu___is_Sig_new_effect: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_new_effect _0 -> true | uu____4068 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_new_effect__item___0: sigelt' -> eff_decl =
  fun projectee  -> match projectee with | Sig_new_effect _0 -> _0
let uu___is_Sig_new_effect_for_free: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Sig_new_effect_for_free _0 -> true
<<<<<<< HEAD
    | uu____3104 -> false
=======
    | uu____4082 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_new_effect_for_free__item___0: sigelt' -> eff_decl =
  fun projectee  -> match projectee with | Sig_new_effect_for_free _0 -> _0
let uu___is_Sig_sub_effect: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_sub_effect _0 -> true | uu____3116 -> false
=======
    match projectee with | Sig_sub_effect _0 -> true | uu____4096 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_sub_effect__item___0: sigelt' -> sub_eff =
  fun projectee  -> match projectee with | Sig_sub_effect _0 -> _0
let uu___is_Sig_effect_abbrev: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_effect_abbrev _0 -> true | uu____3134 -> false
=======
    match projectee with | Sig_effect_abbrev _0 -> true | uu____4116 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_effect_abbrev__item___0:
  sigelt' ->
    (FStar_Ident.lident* univ_names* binders* comp* cflags Prims.list)
  = fun projectee  -> match projectee with | Sig_effect_abbrev _0 -> _0
let uu___is_Sig_pragma: sigelt' -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Sig_pragma _0 -> true | uu____3164 -> false
=======
    match projectee with | Sig_pragma _0 -> true | uu____4148 -> false
>>>>>>> origin/guido_tactics
let __proj__Sig_pragma__item___0: sigelt' -> pragma =
  fun projectee  -> match projectee with | Sig_pragma _0 -> _0
let __proj__Mksigelt__item__sigel: sigelt -> sigelt' =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;_} ->
        __fname__sigel
let __proj__Mksigelt__item__sigrng: sigelt -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;_} ->
        __fname__sigrng
let __proj__Mksigelt__item__sigquals: sigelt -> qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;_} ->
        __fname__sigquals
let __proj__Mksigelt__item__sigmeta: sigelt -> sig_metadata =
  fun projectee  ->
    match projectee with
    | { sigel = __fname__sigel; sigrng = __fname__sigrng;
        sigquals = __fname__sigquals; sigmeta = __fname__sigmeta;_} ->
        __fname__sigmeta
type sigelts = sigelt Prims.list
type modul =
  {
  name: FStar_Ident.lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface: Prims.bool;}
let __proj__Mkmodul__item__name: modul -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__name
let __proj__Mkmodul__item__declarations: modul -> sigelts =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__declarations
let __proj__Mkmodul__item__exports: modul -> sigelts =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__exports
let __proj__Mkmodul__item__is_interface: modul -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; declarations = __fname__declarations;
        exports = __fname__exports; is_interface = __fname__is_interface;_}
        -> __fname__is_interface
type path = Prims.string Prims.list
type subst_t = subst_elt Prims.list
type ('a,'b) mk_t_a = 'b option -> FStar_Range.range -> ('a,'b) syntax
type mk_t = (term',term') mk_t_a
let contains_reflectable: qualifier Prims.list -> Prims.bool =
  fun l  ->
    FStar_Util.for_some
<<<<<<< HEAD
      (fun uu___87_3247  ->
         match uu___87_3247 with
         | Reflectable uu____3248 -> true
         | uu____3249 -> false) l
let withinfo v1 r = { v = v1; p = r }
let withsort v1 = withinfo v1 FStar_Range.dummyRange
=======
      (fun uu___88_4267  ->
         match uu___88_4267 with
         | Reflectable uu____4268 -> true
         | uu____4269 -> false) l
let withinfo v1 s r = { v = v1; ty = s; p = r }
let withsort v1 s = withinfo v1 s FStar_Range.dummyRange
>>>>>>> origin/guido_tactics
let bv_eq: bv -> bv -> Prims.bool =
  fun bv1  ->
    fun bv2  ->
      ((bv1.ppname).FStar_Ident.idText = (bv2.ppname).FStar_Ident.idText) &&
        (bv1.index = bv2.index)
let order_bv: bv -> bv -> Prims.int =
  fun x  ->
    fun y  ->
      let i =
        FStar_String.compare (x.ppname).FStar_Ident.idText
          (y.ppname).FStar_Ident.idText in
      if i = (Prims.parse_int "0") then x.index - y.index else i
let order_fv: FStar_Ident.lident -> FStar_Ident.lident -> Prims.int =
  fun x  ->
    fun y  -> FStar_String.compare x.FStar_Ident.str y.FStar_Ident.str
let range_of_lbname: lbname -> FStar_Range.range =
  fun l  ->
    match l with
    | FStar_Util.Inl x -> (x.ppname).FStar_Ident.idRange
    | FStar_Util.Inr fv -> FStar_Ident.range_of_lid (fv.fv_name).v
let range_of_bv: bv -> FStar_Range.range =
  fun x  -> (x.ppname).FStar_Ident.idRange
let set_range_of_bv: bv -> FStar_Range.range -> bv =
  fun x  ->
    fun r  ->
<<<<<<< HEAD
      let uu___94_3305 = x in
      {
        ppname = (FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r));
        index = (uu___94_3305.index);
        sort = (uu___94_3305.sort)
      }
let syn p k f = f k p
let mk_fvs uu____3346 = FStar_Util.mk_ref None
let mk_uvs uu____3358 = FStar_Util.mk_ref None
let new_bv_set: Prims.unit -> bv FStar_Util.set =
  fun uu____3364  ->
=======
      let uu___95_4364 = x in
      {
        ppname = (FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r));
        index = (uu___95_4364.index);
        sort = (uu___95_4364.sort)
      }
let syn p k f = f k p
let mk_fvs uu____4413 = FStar_Util.mk_ref None
let mk_uvs uu____4427 = FStar_Util.mk_ref None
let new_bv_set: Prims.unit -> bv FStar_Util.set =
  fun uu____4434  ->
>>>>>>> origin/guido_tactics
    FStar_Util.new_set order_bv
      (fun x  ->
         x.index + (FStar_Util.hashcode (x.ppname).FStar_Ident.idText))
let new_fv_set: Prims.unit -> FStar_Ident.lident FStar_Util.set =
<<<<<<< HEAD
  fun uu____3371  ->
=======
  fun uu____4441  ->
>>>>>>> origin/guido_tactics
    FStar_Util.new_set order_fv
      (fun x  -> FStar_Util.hashcode x.FStar_Ident.str)
let new_universe_names_fifo_set:
  Prims.unit -> FStar_Ident.ident FStar_Util.fifo_set =
<<<<<<< HEAD
  fun uu____3380  ->
=======
  fun uu____4450  ->
>>>>>>> origin/guido_tactics
    FStar_Util.new_fifo_set
      (fun x  ->
         fun y  ->
           FStar_String.compare (FStar_Ident.text_of_id x)
             (FStar_Ident.text_of_id y))
      (fun x  -> FStar_Util.hashcode (FStar_Ident.text_of_id x))
let no_names: bv FStar_Util.set = new_bv_set ()
let no_fvars: FStar_Ident.lident FStar_Util.set = new_fv_set ()
let no_universe_names: univ_name FStar_Util.fifo_set =
  new_universe_names_fifo_set ()
let freenames_of_list: bv Prims.list -> bv FStar_Util.set =
  fun l  -> FStar_List.fold_right FStar_Util.set_add l no_names
let list_of_freenames: freenames -> bv Prims.list =
  fun fvs  -> FStar_Util.set_elements fvs
let mk t topt r =
<<<<<<< HEAD
  let uu____3429 = FStar_Util.mk_ref topt in
  let uu____3433 = FStar_Util.mk_ref None in
  { n = t; tk = uu____3429; pos = r; vars = uu____3433 }
let bv_to_tm: bv -> (term',term') syntax =
  fun bv  ->
    let uu____3444 = range_of_bv bv in
    mk (Tm_bvar bv) (Some ((bv.sort).n)) uu____3444
let bv_to_name: bv -> (term',term') syntax =
  fun bv  ->
    let uu____3452 = range_of_bv bv in
    mk (Tm_name bv) (Some ((bv.sort).n)) uu____3452
=======
  let uu____4501 = FStar_Util.mk_ref topt in
  let uu____4505 = FStar_Util.mk_ref None in
  { n = t; tk = uu____4501; pos = r; vars = uu____4505 }
let bv_to_tm: bv -> (term',term') syntax =
  fun bv  ->
    let uu____4517 = range_of_bv bv in
    mk (Tm_bvar bv) (Some ((bv.sort).n)) uu____4517
let bv_to_name: bv -> (term',term') syntax =
  fun bv  ->
    let uu____4526 = range_of_bv bv in
    mk (Tm_name bv) (Some ((bv.sort).n)) uu____4526
>>>>>>> origin/guido_tactics
let mk_Tm_app:
  typ ->
    arg Prims.list ->
      term' option -> FStar_Range.range -> (term',term') syntax
  =
  fun t1  ->
    fun args  ->
      fun k  ->
        fun p  ->
          match args with
          | [] -> t1
<<<<<<< HEAD
          | uu____3473 -> mk (Tm_app (t1, args)) k p
let mk_Tm_uinst: term -> universes -> term =
  fun t  ->
    fun uu___88_3485  ->
      match uu___88_3485 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____3487 -> mk (Tm_uinst (t, us)) None t.pos
           | uu____3492 -> failwith "Unexpected universe instantiation")
=======
          | uu____4549 -> mk (Tm_app (t1, args)) k p
let mk_Tm_uinst: term -> universes -> term =
  fun t  ->
    fun uu___89_4563  ->
      match uu___89_4563 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____4565 -> mk (Tm_uinst (t, us)) None t.pos
           | uu____4570 -> failwith "Unexpected universe instantiation")
>>>>>>> origin/guido_tactics
let extend_app_n:
  term -> args -> term' option -> FStar_Range.range -> (term',term') syntax =
  fun t  ->
    fun args'  ->
      fun kopt  ->
        fun r  ->
          match t.n with
          | Tm_app (head1,args) ->
              mk_Tm_app head1 (FStar_List.append args args') kopt r
<<<<<<< HEAD
          | uu____3530 -> mk_Tm_app t args' kopt r
=======
          | uu____4610 -> mk_Tm_app t args' kopt r
>>>>>>> origin/guido_tactics
let extend_app:
  term -> arg -> term' option -> FStar_Range.range -> (term',term') syntax =
  fun t  -> fun arg  -> fun kopt  -> fun r  -> extend_app_n t [arg] kopt r
let mk_Tm_delayed:
  (term* subst_ts) -> FStar_Range.range -> (term',term') syntax =
  fun lr  ->
    fun pos  ->
<<<<<<< HEAD
      let uu____3567 =
        let uu____3570 =
          let uu____3571 =
            let uu____3592 = FStar_Util.mk_ref None in (lr, uu____3592) in
          Tm_delayed uu____3571 in
        mk uu____3570 in
      uu____3567 None pos
=======
      let uu____4642 =
        let uu____4645 =
          let uu____4646 =
            let uu____4661 = FStar_Util.mk_ref None in (lr, uu____4661) in
          Tm_delayed uu____4646 in
        mk uu____4645 in
      uu____4642 None pos
>>>>>>> origin/guido_tactics
let mk_Total': typ -> universe option -> (comp',Prims.unit) syntax =
  fun t  -> fun u  -> mk (Total (t, u)) None t.pos
let mk_GTotal': typ -> universe option -> (comp',Prims.unit) syntax =
  fun t  -> fun u  -> mk (GTotal (t, u)) None t.pos
let mk_Total: typ -> comp = fun t  -> mk_Total' t None
let mk_GTotal: typ -> comp = fun t  -> mk_GTotal' t None
let mk_Comp: comp_typ -> (comp',Prims.unit) syntax =
  fun ct  -> mk (Comp ct) None (ct.result_typ).pos
let mk_lb:
  (lbname* univ_name Prims.list* FStar_Ident.lident* typ* term) -> letbinding
  =
<<<<<<< HEAD
  fun uu____3670  ->
    match uu____3670 with
=======
  fun uu____4743  ->
    match uu____4743 with
>>>>>>> origin/guido_tactics
    | (x,univs,eff,t,e) ->
        { lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e }
let default_sigmeta: sig_metadata =
  { sigmeta_active = true; sigmeta_fact_db_ids = [] }
let mk_sigelt: sigelt' -> sigelt =
  fun e  ->
    {
      sigel = e;
      sigrng = FStar_Range.dummyRange;
      sigquals = [];
      sigmeta = default_sigmeta
    }
let mk_subst: subst_t -> subst_t = fun s  -> s
let extend_subst: subst_elt -> subst_elt Prims.list -> subst_elt Prims.list =
  fun x  -> fun s  -> x :: s
let argpos: arg -> FStar_Range.range = fun x  -> (fst x).pos
let tun: (term',term') syntax = mk Tm_unknown None FStar_Range.dummyRange
let teff: (term',term') syntax =
  mk (Tm_constant FStar_Const.Const_effect) (Some Tm_unknown)
    FStar_Range.dummyRange
let is_teff: term -> Prims.bool =
  fun t  ->
    match t.n with
    | Tm_constant (FStar_Const.Const_effect ) -> true
<<<<<<< HEAD
    | uu____3718 -> false
let is_type: term -> Prims.bool =
  fun t  -> match t.n with | Tm_type uu____3722 -> true | uu____3723 -> false
=======
    | uu____4797 -> false
let is_type: term -> Prims.bool =
  fun t  -> match t.n with | Tm_type uu____4802 -> true | uu____4803 -> false
>>>>>>> origin/guido_tactics
let null_id: FStar_Ident.ident =
  FStar_Ident.mk_ident ("_", FStar_Range.dummyRange)
let null_bv: term -> bv =
  fun k  -> { ppname = null_id; index = (Prims.parse_int "0"); sort = k }
let mk_binder: bv -> (bv* arg_qualifier option) = fun a  -> (a, None)
let null_binder: term -> (bv* arg_qualifier option) =
<<<<<<< HEAD
  fun t  -> let uu____3734 = null_bv t in (uu____3734, None)
=======
  fun t  -> let uu____4817 = null_bv t in (uu____4817, None)
>>>>>>> origin/guido_tactics
let imp_tag: arg_qualifier = Implicit false
let iarg: term -> (term* arg_qualifier option) =
  fun t  -> (t, (Some imp_tag))
let as_arg: term -> (term* arg_qualifier option) = fun t  -> (t, None)
let is_null_bv: bv -> Prims.bool =
  fun b  -> (b.ppname).FStar_Ident.idText = null_id.FStar_Ident.idText
let is_null_binder: binder -> Prims.bool = fun b  -> is_null_bv (fst b)
let is_top_level: letbinding Prims.list -> Prims.bool =
<<<<<<< HEAD
  fun uu___89_3753  ->
    match uu___89_3753 with
    | { lbname = FStar_Util.Inr uu____3755; lbunivs = uu____3756;
        lbtyp = uu____3757; lbeff = uu____3758; lbdef = uu____3759;_}::uu____3760
        -> true
    | uu____3767 -> false
let freenames_of_binders: binders -> bv FStar_Util.set =
  fun bs  ->
    FStar_List.fold_right
      (fun uu____3779  ->
         fun out  ->
           match uu____3779 with | (x,uu____3786) -> FStar_Util.set_add x out)
=======
  fun uu___90_4841  ->
    match uu___90_4841 with
    | { lbname = FStar_Util.Inr uu____4843; lbunivs = uu____4844;
        lbtyp = uu____4845; lbeff = uu____4846; lbdef = uu____4847;_}::uu____4848
        -> true
    | uu____4855 -> false
let freenames_of_binders: binders -> bv FStar_Util.set =
  fun bs  ->
    FStar_List.fold_right
      (fun uu____4864  ->
         fun out  ->
           match uu____4864 with | (x,uu____4871) -> FStar_Util.set_add x out)
>>>>>>> origin/guido_tactics
      bs no_names
let binders_of_list: bv Prims.list -> (bv* arg_qualifier option) Prims.list =
  fun fvs  -> FStar_All.pipe_right fvs (FStar_List.map (fun t  -> (t, None)))
let binders_of_freenames: freenames -> binders =
  fun fvs  ->
<<<<<<< HEAD
    let uu____3806 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____3806 binders_of_list
let is_implicit: aqual -> Prims.bool =
  fun uu___90_3811  ->
    match uu___90_3811 with
    | Some (Implicit uu____3812) -> true
    | uu____3813 -> false
let as_implicit: Prims.bool -> arg_qualifier option =
  fun uu___91_3816  -> if uu___91_3816 then Some imp_tag else None
=======
    let uu____4892 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____4892 binders_of_list
let is_implicit: aqual -> Prims.bool =
  fun uu___91_4898  ->
    match uu___91_4898 with
    | Some (Implicit uu____4899) -> true
    | uu____4900 -> false
let as_implicit: Prims.bool -> arg_qualifier option =
  fun uu___92_4904  -> if uu___92_4904 then Some imp_tag else None
>>>>>>> origin/guido_tactics
let pat_bvs: pat -> bv Prims.list =
  fun p  ->
    let rec aux b p1 =
      match p1.v with
<<<<<<< HEAD
      | Pat_dot_term uu____3836 -> b
      | Pat_constant uu____3841 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____3844,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____3863  ->
                 match uu____3863 with | (p2,uu____3870) -> aux b1 p2) b pats in
    let uu____3873 = aux [] p in
    FStar_All.pipe_left FStar_List.rev uu____3873
let gen_reset: ((Prims.unit -> Prims.int)* (Prims.unit -> Prims.unit)) =
  let x = FStar_Util.mk_ref (Prims.parse_int "0") in
  let gen1 uu____3889 = FStar_Util.incr x; FStar_ST.read x in
  let reset uu____3899 = FStar_ST.write x (Prims.parse_int "0") in
=======
      | Pat_dot_term uu____4927 -> b
      | Pat_constant uu____4932 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____4935,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____4953  ->
                 match uu____4953 with | (p2,uu____4961) -> aux b1 p2) b pats in
    let uu____4966 = aux [] p in
    FStar_All.pipe_left FStar_List.rev uu____4966
let gen_reset: ((Prims.unit -> Prims.int)* (Prims.unit -> Prims.unit)) =
  let x = FStar_Util.mk_ref (Prims.parse_int "0") in
  let gen1 uu____4982 = FStar_Util.incr x; FStar_ST.read x in
  let reset uu____4992 = FStar_ST.write x (Prims.parse_int "0") in
>>>>>>> origin/guido_tactics
  (gen1, reset)
let next_id: Prims.unit -> Prims.int = fst gen_reset
let reset_gensym: Prims.unit -> Prims.unit = snd gen_reset
let range_of_ropt: FStar_Range.range option -> FStar_Range.range =
<<<<<<< HEAD
  fun uu___92_3921  ->
    match uu___92_3921 with | None  -> FStar_Range.dummyRange | Some r -> r
=======
  fun uu___93_5017  ->
    match uu___93_5017 with | None  -> FStar_Range.dummyRange | Some r -> r
>>>>>>> origin/guido_tactics
let gen_bv: Prims.string -> FStar_Range.range option -> typ -> bv =
  fun s  ->
    fun r  ->
      fun t  ->
        let id = FStar_Ident.mk_ident (s, (range_of_ropt r)) in
<<<<<<< HEAD
        let uu____3936 = next_id () in
        { ppname = id; index = uu____3936; sort = t }
=======
        let uu____5035 = next_id () in
        { ppname = id; index = uu____5035; sort = t }
>>>>>>> origin/guido_tactics
let new_bv: FStar_Range.range option -> typ -> bv =
  fun ropt  -> fun t  -> gen_bv FStar_Ident.reserved_prefix ropt t
let freshen_bv: bv -> bv =
  fun bv  ->
<<<<<<< HEAD
    let uu____3948 = is_null_bv bv in
    if uu____3948
    then
      let uu____3949 = let uu____3951 = range_of_bv bv in Some uu____3951 in
      new_bv uu____3949 bv.sort
    else
      (let uu___95_3953 = bv in
       let uu____3954 = next_id () in
       {
         ppname = (uu___95_3953.ppname);
         index = uu____3954;
         sort = (uu___95_3953.sort)
=======
    let uu____5050 = is_null_bv bv in
    if uu____5050
    then
      let uu____5051 = let uu____5053 = range_of_bv bv in Some uu____5053 in
      new_bv uu____5051 bv.sort
    else
      (let uu___96_5055 = bv in
       let uu____5056 = next_id () in
       {
         ppname = (uu___96_5055.ppname);
         index = uu____5056;
         sort = (uu___96_5055.sort)
>>>>>>> origin/guido_tactics
       })
let new_univ_name: FStar_Range.range option -> FStar_Ident.ident =
  fun ropt  ->
    let id = next_id () in
<<<<<<< HEAD
    let uu____3961 =
      let uu____3964 =
        let uu____3965 = FStar_Util.string_of_int id in
        Prims.strcat FStar_Ident.reserved_prefix uu____3965 in
      (uu____3964, (range_of_ropt ropt)) in
    FStar_Ident.mk_ident uu____3961
=======
    let uu____5064 =
      let uu____5067 =
        let uu____5068 = FStar_Util.string_of_int id in
        Prims.strcat FStar_Ident.reserved_prefix uu____5068 in
      (uu____5067, (range_of_ropt ropt)) in
    FStar_Ident.mk_ident uu____5064
>>>>>>> origin/guido_tactics
let mkbv: FStar_Ident.ident -> Prims.int -> (term',term') syntax -> bv =
  fun x  -> fun y  -> fun t  -> { ppname = x; index = y; sort = t }
let lbname_eq:
  (bv,FStar_Ident.lident) FStar_Util.either ->
    (bv,FStar_Ident.lident) FStar_Util.either -> Prims.bool
  =
  fun l1  ->
    fun l2  ->
      match (l1, l2) with
      | (FStar_Util.Inl x,FStar_Util.Inl y) -> bv_eq x y
      | (FStar_Util.Inr l,FStar_Util.Inr m) -> FStar_Ident.lid_equals l m
<<<<<<< HEAD
      | uu____4009 -> false
=======
      | uu____5117 -> false
>>>>>>> origin/guido_tactics
let fv_eq: fv -> fv -> Prims.bool =
  fun fv1  ->
    fun fv2  -> FStar_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
let fv_eq_lid: fv -> FStar_Ident.lident -> Prims.bool =
  fun fv  -> fun lid  -> FStar_Ident.lid_equals (fv.fv_name).v lid
let set_bv_range: bv -> FStar_Range.range -> bv =
  fun bv  ->
    fun r  ->
<<<<<<< HEAD
      let uu___96_4034 = bv in
      {
        ppname = (FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r));
        index = (uu___96_4034.index);
        sort = (uu___96_4034.sort)
=======
      let uu___97_5160 = bv in
      {
        ppname = (FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r));
        index = (uu___97_5160.index);
        sort = (uu___97_5160.sort)
>>>>>>> origin/guido_tactics
      }
let lid_as_fv: FStar_Ident.lident -> delta_depth -> fv_qual option -> fv =
  fun l  ->
    fun dd  ->
      fun dq  ->
<<<<<<< HEAD
        let uu____4046 = withinfo l (FStar_Ident.range_of_lid l) in
        { fv_name = uu____4046; fv_delta = dd; fv_qual = dq }
=======
        let uu____5175 = withinfo l tun (FStar_Ident.range_of_lid l) in
        { fv_name = uu____5175; fv_delta = dd; fv_qual = dq }
>>>>>>> origin/guido_tactics
let fv_to_tm: fv -> (term',term') syntax =
  fun fv  -> mk (Tm_fvar fv) None (FStar_Ident.range_of_lid (fv.fv_name).v)
let fvar: FStar_Ident.lident -> delta_depth -> fv_qual option -> term =
  fun l  ->
    fun dd  ->
<<<<<<< HEAD
      fun dq  -> let uu____4065 = lid_as_fv l dd dq in fv_to_tm uu____4065
let lid_of_fv: fv -> FStar_Ident.lident = fun fv  -> (fv.fv_name).v
let range_of_fv: fv -> FStar_Range.range =
  fun fv  ->
    let uu____4072 = lid_of_fv fv in FStar_Ident.range_of_lid uu____4072
let set_range_of_fv: fv -> FStar_Range.range -> fv =
  fun fv  ->
    fun r  ->
      let uu___97_4079 = fv in
      let uu____4080 =
        let uu___98_4081 = fv.fv_name in
        let uu____4082 =
          let uu____4083 = lid_of_fv fv in
          FStar_Ident.set_lid_range uu____4083 r in
        { v = uu____4082; p = (uu___98_4081.p) } in
      {
        fv_name = uu____4080;
        fv_delta = (uu___97_4079.fv_delta);
        fv_qual = (uu___97_4079.fv_qual)
=======
      fun dq  -> let uu____5210 = lid_as_fv l dd dq in fv_to_tm uu____5210
let lid_of_fv: fv -> FStar_Ident.lident = fun fv  -> (fv.fv_name).v
let range_of_fv: fv -> FStar_Range.range =
  fun fv  ->
    let uu____5223 = lid_of_fv fv in FStar_Ident.range_of_lid uu____5223
let set_range_of_fv: fv -> FStar_Range.range -> fv =
  fun fv  ->
    fun r  ->
      let uu___98_5232 = fv in
      let uu____5233 =
        let uu___99_5237 = fv.fv_name in
        let uu____5242 =
          let uu____5243 = lid_of_fv fv in
          FStar_Ident.set_lid_range uu____5243 r in
        { v = uu____5242; ty = (uu___99_5237.ty); p = (uu___99_5237.p) } in
      {
        fv_name = uu____5233;
        fv_delta = (uu___98_5232.fv_delta);
        fv_qual = (uu___98_5232.fv_qual)
>>>>>>> origin/guido_tactics
      }
let has_simple_attribute: term Prims.list -> Prims.string -> Prims.bool =
  fun l  ->
    fun s  ->
      FStar_List.existsb
<<<<<<< HEAD
        (fun uu___93_4100  ->
           match uu___93_4100 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____4104));
               tk = uu____4105; pos = uu____4106; vars = uu____4107;_} when
               (FStar_Util.string_of_unicode data) = s -> true
           | uu____4112 -> false) l
=======
        (fun uu___94_5269  ->
           match uu___94_5269 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____5273));
               tk = uu____5274; pos = uu____5275; vars = uu____5276;_} when
               (FStar_Util.string_of_unicode data) = s -> true
           | uu____5281 -> false) l
>>>>>>> origin/guido_tactics
