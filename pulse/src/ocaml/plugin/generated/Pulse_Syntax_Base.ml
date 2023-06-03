open Prims
type constant = FStar_Reflection_Data.vconst
type var = Prims.nat
type index = Prims.nat
type universe = FStar_Reflection_Types.universe
type ppname = FStar_Reflection_Typing.pp_name_t
type 'r range_singleton_trigger = unit
type range = FStar_Range.range
type bv = {
  bv_index: index ;
  bv_ppname: ppname ;
  bv_range: range }
let (__proj__Mkbv__item__bv_index : bv -> index) =
  fun projectee ->
    match projectee with | { bv_index; bv_ppname; bv_range;_} -> bv_index
let (__proj__Mkbv__item__bv_ppname : bv -> ppname) =
  fun projectee ->
    match projectee with | { bv_index; bv_ppname; bv_range;_} -> bv_ppname
let (__proj__Mkbv__item__bv_range : bv -> range) =
  fun projectee ->
    match projectee with | { bv_index; bv_ppname; bv_range;_} -> bv_range
type nm = {
  nm_index: var ;
  nm_ppname: ppname ;
  nm_range: range }
let (__proj__Mknm__item__nm_index : nm -> var) =
  fun projectee ->
    match projectee with | { nm_index; nm_ppname; nm_range;_} -> nm_index
let (__proj__Mknm__item__nm_ppname : nm -> ppname) =
  fun projectee ->
    match projectee with | { nm_index; nm_ppname; nm_range;_} -> nm_ppname
let (__proj__Mknm__item__nm_range : nm -> range) =
  fun projectee ->
    match projectee with | { nm_index; nm_ppname; nm_range;_} -> nm_range
type qualifier =
  | Implicit 
let (uu___is_Implicit : qualifier -> Prims.bool) = fun projectee -> true
type should_check_t = (Prims.bool, unit) FStar_Sealed_Inhabited.sealed
let (should_check_true : should_check_t) =
  FStar_Sealed_Inhabited.seal false true
let (should_check_false : should_check_t) =
  FStar_Sealed_Inhabited.seal false false
type fv = {
  fv_name: FStar_Reflection_Types.name ;
  fv_range: range }
let (__proj__Mkfv__item__fv_name : fv -> FStar_Reflection_Types.name) =
  fun projectee -> match projectee with | { fv_name; fv_range;_} -> fv_name
let (__proj__Mkfv__item__fv_range : fv -> range) =
  fun projectee -> match projectee with | { fv_name; fv_range;_} -> fv_range
let (as_fv : FStar_Reflection_Types.name -> fv) =
  fun l -> { fv_name = l; fv_range = FStar_Range.range_0 }
type 't not_tv_unknown = unit
type host_term = FStar_Reflection_Types.term
type term =
  | Tm_Emp 
  | Tm_Pure of term 
  | Tm_Star of term * term 
  | Tm_ExistsSL of universe * term * term 
  | Tm_ForallSL of universe * term * term 
  | Tm_VProp 
  | Tm_Inames 
  | Tm_EmpInames 
  | Tm_FStar of host_term * range 
  | Tm_Unknown 
let uu___is_Tm_Emp uu___ = match uu___ with | Tm_Emp _ -> true | _ -> false
let uu___is_Tm_Pure uu___ = match uu___ with | Tm_Pure _ -> true | _ -> false
let uu___is_Tm_Star uu___ = match uu___ with | Tm_Star _ -> true | _ -> false
let uu___is_Tm_ExistsSL uu___ =
  match uu___ with | Tm_ExistsSL _ -> true | _ -> false
let uu___is_Tm_ForallSL uu___ =
  match uu___ with | Tm_ForallSL _ -> true | _ -> false
let uu___is_Tm_VProp uu___ =
  match uu___ with | Tm_VProp _ -> true | _ -> false
let uu___is_Tm_Inames uu___ =
  match uu___ with | Tm_Inames _ -> true | _ -> false
let uu___is_Tm_EmpInames uu___ =
  match uu___ with | Tm_EmpInames _ -> true | _ -> false
let uu___is_Tm_FStar uu___ =
  match uu___ with | Tm_FStar _ -> true | _ -> false
let uu___is_Tm_Unknown uu___ =
  match uu___ with | Tm_Unknown _ -> true | _ -> false
type vprop = term
type binder = {
  binder_ty: term ;
  binder_ppname: ppname }
let (__proj__Mkbinder__item__binder_ty : binder -> term) =
  fun projectee ->
    match projectee with | { binder_ty; binder_ppname;_} -> binder_ty
let (__proj__Mkbinder__item__binder_ppname : binder -> ppname) =
  fun projectee ->
    match projectee with | { binder_ty; binder_ppname;_} -> binder_ppname
type st_comp = {
  u: universe ;
  res: term ;
  pre: vprop ;
  post: vprop }
let (__proj__Mkst_comp__item__u : st_comp -> universe) =
  fun projectee -> match projectee with | { u; res; pre; post;_} -> u
let (__proj__Mkst_comp__item__res : st_comp -> term) =
  fun projectee -> match projectee with | { u; res; pre; post;_} -> res
let (__proj__Mkst_comp__item__pre : st_comp -> vprop) =
  fun projectee -> match projectee with | { u; res; pre; post;_} -> pre
let (__proj__Mkst_comp__item__post : st_comp -> vprop) =
  fun projectee -> match projectee with | { u; res; pre; post;_} -> post
type comp =
  | C_Tot of term 
  | C_ST of st_comp 
  | C_STAtomic of term * st_comp 
  | C_STGhost of term * st_comp 
let (uu___is_C_Tot : comp -> Prims.bool) =
  fun projectee -> match projectee with | C_Tot _0 -> true | uu___ -> false
let (__proj__C_Tot__item___0 : comp -> term) =
  fun projectee -> match projectee with | C_Tot _0 -> _0
let (uu___is_C_ST : comp -> Prims.bool) =
  fun projectee -> match projectee with | C_ST _0 -> true | uu___ -> false
let (__proj__C_ST__item___0 : comp -> st_comp) =
  fun projectee -> match projectee with | C_ST _0 -> _0
let (uu___is_C_STAtomic : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | C_STAtomic (_0, _1) -> true | uu___ -> false
let (__proj__C_STAtomic__item___0 : comp -> term) =
  fun projectee -> match projectee with | C_STAtomic (_0, _1) -> _0
let (__proj__C_STAtomic__item___1 : comp -> st_comp) =
  fun projectee -> match projectee with | C_STAtomic (_0, _1) -> _1
let (uu___is_C_STGhost : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | C_STGhost (_0, _1) -> true | uu___ -> false
let (__proj__C_STGhost__item___0 : comp -> term) =
  fun projectee -> match projectee with | C_STGhost (_0, _1) -> _0
let (__proj__C_STGhost__item___1 : comp -> st_comp) =
  fun projectee -> match projectee with | C_STGhost (_0, _1) -> _1
type comp_st = comp
type ctag =
  | STT 
  | STT_Atomic 
  | STT_Ghost 
let (uu___is_STT : ctag -> Prims.bool) =
  fun projectee -> match projectee with | STT -> true | uu___ -> false
let (uu___is_STT_Atomic : ctag -> Prims.bool) =
  fun projectee -> match projectee with | STT_Atomic -> true | uu___ -> false
let (uu___is_STT_Ghost : ctag -> Prims.bool) =
  fun projectee -> match projectee with | STT_Ghost -> true | uu___ -> false
type st_term'__Tm_Return__payload =
  {
  ctag: ctag ;
  insert_eq: Prims.bool ;
  term: term }
and st_term'__Tm_Abs__payload =
  {
  b: binder ;
  q: qualifier FStar_Pervasives_Native.option ;
  pre1: vprop FStar_Pervasives_Native.option ;
  body: st_term ;
  ret_ty: term FStar_Pervasives_Native.option ;
  post1: vprop FStar_Pervasives_Native.option }
and st_term'__Tm_STApp__payload =
  {
  head: term ;
  arg_qual: qualifier FStar_Pervasives_Native.option ;
  arg: term }
and st_term'__Tm_Bind__payload =
  {
  binder: binder ;
  head1: st_term ;
  body1: st_term }
and st_term'__Tm_TotBind__payload = {
  head2: term ;
  body2: st_term }
and st_term'__Tm_If__payload =
  {
  b1: term ;
  then_: st_term ;
  else_: st_term ;
  post2: vprop FStar_Pervasives_Native.option }
and st_term'__Tm_IntroPure__payload =
  {
  p: term ;
  should_check: should_check_t }
and st_term'__Tm_ElimExists__payload = {
  p1: vprop }
and st_term'__Tm_IntroExists__payload =
  {
  erased: Prims.bool ;
  p2: vprop ;
  witnesses: term Prims.list ;
  should_check1: should_check_t }
and st_term'__Tm_While__payload =
  {
  invariant: term ;
  condition: st_term ;
  body3: st_term }
and st_term'__Tm_Par__payload =
  {
  pre11: term ;
  body11: st_term ;
  post11: term ;
  pre2: term ;
  body21: st_term ;
  post21: term }
and st_term'__Tm_WithLocal__payload = {
  initializer1: term ;
  body4: st_term }
and st_term'__Tm_Rewrite__payload = {
  t1: term ;
  t2: term }
and st_term'__Tm_Admit__payload =
  {
  ctag1: ctag ;
  u1: universe ;
  typ: term ;
  post3: term FStar_Pervasives_Native.option }
and st_term'__Tm_Protect__payload = {
  t: st_term }
and st_term' =
  | Tm_Return of st_term'__Tm_Return__payload 
  | Tm_Abs of st_term'__Tm_Abs__payload 
  | Tm_STApp of st_term'__Tm_STApp__payload 
  | Tm_Bind of st_term'__Tm_Bind__payload 
  | Tm_TotBind of st_term'__Tm_TotBind__payload 
  | Tm_If of st_term'__Tm_If__payload 
  | Tm_IntroPure of st_term'__Tm_IntroPure__payload 
  | Tm_ElimExists of st_term'__Tm_ElimExists__payload 
  | Tm_IntroExists of st_term'__Tm_IntroExists__payload 
  | Tm_While of st_term'__Tm_While__payload 
  | Tm_Par of st_term'__Tm_Par__payload 
  | Tm_WithLocal of st_term'__Tm_WithLocal__payload 
  | Tm_Rewrite of st_term'__Tm_Rewrite__payload 
  | Tm_Admit of st_term'__Tm_Admit__payload 
  | Tm_Protect of st_term'__Tm_Protect__payload 
and st_term = {
  term1: st_term' ;
  range: range }
let uu___is_Tm_Return uu___ =
  match uu___ with | Tm_Return _ -> true | _ -> false
let uu___is_Tm_Abs uu___ = match uu___ with | Tm_Abs _ -> true | _ -> false
let uu___is_Tm_STApp uu___ =
  match uu___ with | Tm_STApp _ -> true | _ -> false
let uu___is_Tm_Bind uu___ = match uu___ with | Tm_Bind _ -> true | _ -> false
let uu___is_Tm_TotBind uu___ =
  match uu___ with | Tm_TotBind _ -> true | _ -> false
let uu___is_Tm_If uu___ = match uu___ with | Tm_If _ -> true | _ -> false
let uu___is_Tm_IntroPure uu___ =
  match uu___ with | Tm_IntroPure _ -> true | _ -> false
let uu___is_Tm_ElimExists uu___ =
  match uu___ with | Tm_ElimExists _ -> true | _ -> false
let uu___is_Tm_IntroExists uu___ =
  match uu___ with | Tm_IntroExists _ -> true | _ -> false
let uu___is_Tm_While uu___ =
  match uu___ with | Tm_While _ -> true | _ -> false
let uu___is_Tm_Par uu___ = match uu___ with | Tm_Par _ -> true | _ -> false
let uu___is_Tm_WithLocal uu___ =
  match uu___ with | Tm_WithLocal _ -> true | _ -> false
let uu___is_Tm_Rewrite uu___ =
  match uu___ with | Tm_Rewrite _ -> true | _ -> false
let uu___is_Tm_Admit uu___ =
  match uu___ with | Tm_Admit _ -> true | _ -> false
let uu___is_Tm_Protect uu___ =
  match uu___ with | Tm_Protect _ -> true | _ -> false
let (null_binder : term -> binder) =
  fun t ->
    { binder_ty = t; binder_ppname = FStar_Reflection_Typing.pp_name_default
    }
let (mk_binder : Prims.string -> term -> binder) =
  fun s ->
    fun t ->
      {
        binder_ty = t;
        binder_ppname = (FStar_Reflection_Typing.seal_pp_name s)
      }
let (eq_univ : universe -> universe -> Prims.bool) =
  fun u1 ->
    fun u2 ->
      FStar_Reflection_Builtins.term_eq
        (FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_Type u1))
        (FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_Type u2))
let rec (eq_tm : term -> term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (Tm_VProp, Tm_VProp) -> true
      | (Tm_Emp, Tm_Emp) -> true
      | (Tm_Inames, Tm_Inames) -> true
      | (Tm_EmpInames, Tm_EmpInames) -> true
      | (Tm_Unknown, Tm_Unknown) -> true
      | (Tm_Star (l1, r1), Tm_Star (l2, r2)) ->
          (eq_tm l1 l2) && (eq_tm r1 r2)
      | (Tm_Pure p1, Tm_Pure p2) -> eq_tm p1 p2
      | (Tm_ExistsSL (u1, t11, b1), Tm_ExistsSL (u2, t21, b2)) ->
          ((eq_univ u1 u2) && (eq_tm t11 t21)) && (eq_tm b1 b2)
      | (Tm_ForallSL (u1, t11, b1), Tm_ForallSL (u2, t21, b2)) ->
          ((eq_univ u1 u2) && (eq_tm t11 t21)) && (eq_tm b1 b2)
      | (Tm_FStar (t11, r), Tm_FStar (t21, uu___)) ->
          FStar_Reflection_Builtins.term_eq t11 t21
      | uu___ -> false
let (eq_st_comp : st_comp -> st_comp -> Prims.bool) =
  fun s1 ->
    fun s2 ->
      (((eq_univ s1.u s2.u) && (eq_tm s1.res s2.res)) &&
         (eq_tm s1.pre s2.pre))
        && (eq_tm s1.post s2.post)
let (eq_comp : comp -> comp -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (C_Tot t1, C_Tot t2) -> eq_tm t1 t2
      | (C_ST s1, C_ST s2) -> eq_st_comp s1 s2
      | (C_STAtomic (i1, s1), C_STAtomic (i2, s2)) ->
          (eq_tm i1 i2) && (eq_st_comp s1 s2)
      | (C_STGhost (i1, s1), C_STGhost (i2, s2)) ->
          (eq_tm i1 i2) && (eq_st_comp s1 s2)
      | uu___ -> false
let (eq_tm_opt :
  term FStar_Pervasives_Native.option ->
    term FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
      | (FStar_Pervasives_Native.Some t11, FStar_Pervasives_Native.Some t21)
          -> eq_tm t11 t21
      | uu___ -> false
let rec (eq_tm_list : term Prims.list -> term Prims.list -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | ([], []) -> true
      | (h1::t11, h2::t21) -> (eq_tm h1 h2) && (eq_tm_list t11 t21)
      | uu___ -> false
let rec (eq_st_term : st_term -> st_term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match ((t1.term1), (t2.term1)) with
      | (Tm_Return { ctag = c1; insert_eq = b1; term = t11;_}, Tm_Return
         { ctag = c2; insert_eq = b2; term = t21;_}) ->
          ((c1 = c2) && (b1 = b2)) && (eq_tm t11 t21)
      | (Tm_Abs
         { b = b1; q = o1; pre1 = p1; body = t11; ret_ty = r1; post1 = q1;_},
         Tm_Abs
         { b = b2; q = o2; pre1 = p2; body = t21; ret_ty = r2; post1 = q2;_})
          ->
          (((((eq_tm b1.binder_ty b2.binder_ty) && (o1 = o2)) &&
               (eq_tm_opt p1 p2))
              && (eq_st_term t11 t21))
             && (eq_tm_opt r1 r2))
            && (eq_tm_opt q1 q2)
      | (Tm_STApp { head = h1; arg_qual = o1; arg = t11;_}, Tm_STApp
         { head = h2; arg_qual = o2; arg = t21;_}) ->
          ((eq_tm h1 h2) && (o1 = o2)) && (eq_tm t11 t21)
      | (Tm_Bind { binder = b1; head1 = t11; body1 = k1;_}, Tm_Bind
         { binder = b2; head1 = t21; body1 = k2;_}) ->
          ((eq_tm b1.binder_ty b2.binder_ty) && (eq_st_term t11 t21)) &&
            (eq_st_term k1 k2)
      | (Tm_TotBind { head2 = t11; body2 = k1;_}, Tm_TotBind
         { head2 = t21; body2 = k2;_}) ->
          (eq_tm t11 t21) && (eq_st_term k1 k2)
      | (Tm_IntroPure { p = p1; should_check = uu___;_}, Tm_IntroPure
         { p = p2; should_check = uu___1;_}) -> eq_tm p1 p2
      | (Tm_IntroExists
         { erased = b1; p2 = p1; witnesses = l1; should_check1 = uu___;_},
         Tm_IntroExists
         { erased = b2; p2; witnesses = l2; should_check1 = uu___1;_}) ->
          ((b1 = b2) && (eq_tm p1 p2)) && (eq_tm_list l1 l2)
      | (Tm_ElimExists { p1;_}, Tm_ElimExists { p1 = p2;_}) -> eq_tm p1 p2
      | (Tm_If { b1 = g1; then_ = ethen1; else_ = eelse1; post2 = p1;_},
         Tm_If { b1 = g2; then_ = ethen2; else_ = eelse2; post2 = p2;_}) ->
          (((eq_tm g1 g2) && (eq_st_term ethen1 ethen2)) &&
             (eq_st_term eelse1 eelse2))
            && (eq_tm_opt p1 p2)
      | (Tm_While { invariant = inv1; condition = cond1; body3 = body1;_},
         Tm_While { invariant = inv2; condition = cond2; body3 = body2;_}) ->
          ((eq_tm inv1 inv2) && (eq_st_term cond1 cond2)) &&
            (eq_st_term body1 body2)
      | (Tm_Par
         { pre11 = preL1; body11 = eL1; post11 = postL1; pre2 = preR1;
           body21 = eR1; post21 = postR1;_},
         Tm_Par
         { pre11 = preL2; body11 = eL2; post11 = postL2; pre2 = preR2;
           body21 = eR2; post21 = postR2;_})
          ->
          (((((eq_tm preL1 preL2) && (eq_st_term eL1 eL2)) &&
               (eq_tm postL1 postL2))
              && (eq_tm preR1 preR2))
             && (eq_st_term eR1 eR2))
            && (eq_tm postR1 postR2)
      | (Tm_WithLocal { initializer1 = e1; body4 = b1;_}, Tm_WithLocal
         { initializer1 = e2; body4 = b2;_}) ->
          (eq_tm e1 e2) && (eq_st_term b1 b2)
      | (Tm_Rewrite { t1 = l1; t2 = r1;_}, Tm_Rewrite { t1 = l2; t2 = r2;_})
          -> (eq_tm l1 l2) && (eq_tm r1 r2)
      | (Tm_Admit { ctag1 = c1; u1; typ = t11; post3 = post1;_}, Tm_Admit
         { ctag1 = c2; u1 = u2; typ = t21; post3 = post2;_}) ->
          (((c1 = c2) && (eq_univ u1 u2)) && (eq_tm t11 t21)) &&
            (eq_tm_opt post1 post2)
      | (Tm_Protect { t = t11;_}, Tm_Protect { t = t21;_}) ->
          eq_st_term t11 t21
      | uu___ -> false
let (comp_res : comp -> term) =
  fun c ->
    match c with
    | C_Tot ty -> ty
    | C_ST s -> s.res
    | C_STAtomic (uu___, s) -> s.res
    | C_STGhost (uu___, s) -> s.res
let (stateful_comp : comp -> Prims.bool) =
  fun c ->
    ((uu___is_C_ST c) || (uu___is_C_STAtomic c)) || (uu___is_C_STGhost c)
let (st_comp_of_comp : comp -> st_comp) =
  fun c ->
    match c with
    | C_ST s -> s
    | C_STAtomic (uu___, s) -> s
    | C_STGhost (uu___, s) -> s
let (with_st_comp : comp -> st_comp -> comp) =
  fun c ->
    fun s ->
      match c with
      | C_ST uu___ -> C_ST s
      | C_STAtomic (inames, uu___) -> C_STAtomic (inames, s)
      | C_STGhost (inames, uu___) -> C_STGhost (inames, s)
let (comp_u : comp -> universe) =
  fun c ->
    match c with
    | C_ST s -> s.u
    | C_STAtomic (uu___, s) -> s.u
    | C_STGhost (uu___, s) -> s.u
let (comp_pre : comp -> vprop) =
  fun c ->
    match c with
    | C_ST s -> s.pre
    | C_STAtomic (uu___, s) -> s.pre
    | C_STGhost (uu___, s) -> s.pre
let (comp_post : comp -> vprop) =
  fun c ->
    match c with
    | C_ST s -> s.post
    | C_STAtomic (uu___, s) -> s.post
    | C_STGhost (uu___, s) -> s.post
let (comp_inames : comp -> term) =
  fun c ->
    match c with
    | C_STAtomic (inames, uu___) -> inames
    | C_STGhost (inames, uu___) -> inames
type nvar = (ppname * var)
let v_as_nv : 'uuuuu . 'uuuuu -> (FStar_Reflection_Typing.pp_name_t * 'uuuuu)
  = fun x -> (FStar_Reflection_Typing.pp_name_default, x)