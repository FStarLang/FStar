open Prims
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of Prims.int 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> true | uu___ -> false
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu___ -> false
let (__proj__Int__item___0 : constant -> Prims.int) =
  fun projectee -> match projectee with | Int _0 -> _0
type var = Prims.nat
type index = Prims.nat
type universe =
  | U_zero 
  | U_succ of universe 
  | U_var of Prims.string 
  | U_max of universe * universe 
  | U_unknown 
let (uu___is_U_zero : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_zero -> true | uu___ -> false
let (uu___is_U_succ : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_succ _0 -> true | uu___ -> false
let (__proj__U_succ__item___0 : universe -> universe) =
  fun projectee -> match projectee with | U_succ _0 -> _0
let (uu___is_U_var : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_var _0 -> true | uu___ -> false
let (__proj__U_var__item___0 : universe -> Prims.string) =
  fun projectee -> match projectee with | U_var _0 -> _0
let (uu___is_U_max : universe -> Prims.bool) =
  fun projectee ->
    match projectee with | U_max (_0, _1) -> true | uu___ -> false
let (__proj__U_max__item___0 : universe -> universe) =
  fun projectee -> match projectee with | U_max (_0, _1) -> _0
let (__proj__U_max__item___1 : universe -> universe) =
  fun projectee -> match projectee with | U_max (_0, _1) -> _1
let (uu___is_U_unknown : universe -> Prims.bool) =
  fun projectee -> match projectee with | U_unknown -> true | uu___ -> false
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
type should_elim_t = (Prims.bool, unit) FStar_Sealed_Inhabited.sealed
let (should_elim_true : should_elim_t) =
  FStar_Sealed_Inhabited.seal false true
let (should_elim_false : should_elim_t) =
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
  | Tm_BVar of bv 
  | Tm_Var of nm 
  | Tm_FVar of fv 
  | Tm_UInst of fv * universe Prims.list 
  | Tm_Constant of constant 
  | Tm_Refine of binder * term 
  | Tm_PureApp of term * qualifier FStar_Pervasives_Native.option * term 
  | Tm_Let of term * term * term 
  | Tm_Emp 
  | Tm_Pure of term 
  | Tm_Star of term * term 
  | Tm_ExistsSL of universe * term * term * should_elim_t 
  | Tm_ForallSL of universe * term * term 
  | Tm_Arrow of binder * qualifier FStar_Pervasives_Native.option * comp 
  | Tm_Type of universe 
  | Tm_VProp 
  | Tm_Inames 
  | Tm_EmpInames 
  | Tm_UVar of Prims.int 
  | Tm_FStar of host_term 
  | Tm_Unknown 
and binder = {
  binder_ty: term ;
  binder_ppname: ppname }
and comp =
  | C_Tot of term 
  | C_ST of st_comp 
  | C_STAtomic of term * st_comp 
  | C_STGhost of term * st_comp 
and st_comp = {
  u: universe ;
  res: term ;
  pre: term ;
  post: term }
let uu___is_Tm_BVar uu___ = match uu___ with | Tm_BVar _ -> true | _ -> false
let uu___is_Tm_Var uu___ = match uu___ with | Tm_Var _ -> true | _ -> false
let uu___is_Tm_FVar uu___ = match uu___ with | Tm_FVar _ -> true | _ -> false
let uu___is_Tm_UInst uu___ =
  match uu___ with | Tm_UInst _ -> true | _ -> false
let uu___is_Tm_Constant uu___ =
  match uu___ with | Tm_Constant _ -> true | _ -> false
let uu___is_Tm_Refine uu___ =
  match uu___ with | Tm_Refine _ -> true | _ -> false
let uu___is_Tm_PureApp uu___ =
  match uu___ with | Tm_PureApp _ -> true | _ -> false
let uu___is_Tm_Let uu___ = match uu___ with | Tm_Let _ -> true | _ -> false
let uu___is_Tm_Emp uu___ = match uu___ with | Tm_Emp _ -> true | _ -> false
let uu___is_Tm_Pure uu___ = match uu___ with | Tm_Pure _ -> true | _ -> false
let uu___is_Tm_Star uu___ = match uu___ with | Tm_Star _ -> true | _ -> false
let uu___is_Tm_ExistsSL uu___ =
  match uu___ with | Tm_ExistsSL _ -> true | _ -> false
let uu___is_Tm_ForallSL uu___ =
  match uu___ with | Tm_ForallSL _ -> true | _ -> false
let uu___is_Tm_Arrow uu___ =
  match uu___ with | Tm_Arrow _ -> true | _ -> false
let uu___is_Tm_Type uu___ = match uu___ with | Tm_Type _ -> true | _ -> false
let uu___is_Tm_VProp uu___ =
  match uu___ with | Tm_VProp _ -> true | _ -> false
let uu___is_Tm_Inames uu___ =
  match uu___ with | Tm_Inames _ -> true | _ -> false
let uu___is_Tm_EmpInames uu___ =
  match uu___ with | Tm_EmpInames _ -> true | _ -> false
let uu___is_Tm_UVar uu___ = match uu___ with | Tm_UVar _ -> true | _ -> false
let uu___is_Tm_FStar uu___ =
  match uu___ with | Tm_FStar _ -> true | _ -> false
let uu___is_Tm_Unknown uu___ =
  match uu___ with | Tm_Unknown _ -> true | _ -> false
let uu___is_C_Tot uu___ = match uu___ with | C_Tot _ -> true | _ -> false
let uu___is_C_ST uu___ = match uu___ with | C_ST _ -> true | _ -> false
let uu___is_C_STAtomic uu___ =
  match uu___ with | C_STAtomic _ -> true | _ -> false
let uu___is_C_STGhost uu___ =
  match uu___ with | C_STGhost _ -> true | _ -> false
type vprop = term
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
type st_term =
  | Tm_Return of ctag * Prims.bool * term 
  | Tm_Abs of binder * qualifier FStar_Pervasives_Native.option * vprop
  FStar_Pervasives_Native.option * st_term * vprop
  FStar_Pervasives_Native.option 
  | Tm_STApp of term * qualifier FStar_Pervasives_Native.option * term 
  | Tm_Bind of binder * st_term * st_term 
  | Tm_If of term * st_term * st_term * vprop FStar_Pervasives_Native.option
  
  | Tm_ElimExists of vprop 
  | Tm_IntroExists of Prims.bool * vprop * term Prims.list 
  | Tm_While of term * st_term * st_term 
  | Tm_Par of term * st_term * term * term * st_term * term 
  | Tm_WithLocal of term * st_term 
  | Tm_Rewrite of term * term 
  | Tm_Admit of ctag * universe * term * term FStar_Pervasives_Native.option
  
  | Tm_Protect of st_term 
let uu___is_Tm_Return uu___ =
  match uu___ with | Tm_Return _ -> true | _ -> false
let uu___is_Tm_Abs uu___ = match uu___ with | Tm_Abs _ -> true | _ -> false
let uu___is_Tm_STApp uu___ =
  match uu___ with | Tm_STApp _ -> true | _ -> false
let uu___is_Tm_Bind uu___ = match uu___ with | Tm_Bind _ -> true | _ -> false
let uu___is_Tm_If uu___ = match uu___ with | Tm_If _ -> true | _ -> false
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
let (mk_bvar : Prims.string -> FStar_Range.range -> index -> term) =
  fun s ->
    fun r ->
      fun i ->
        Tm_BVar
          {
            bv_index = i;
            bv_ppname = (FStar_Reflection_Typing.seal_pp_name s);
            bv_range = r
          }
let (null_var : var -> term) =
  fun v ->
    Tm_Var
      {
        nm_index = v;
        nm_ppname = FStar_Reflection_Typing.pp_name_default;
        nm_range = FStar_Range.range_0
      }
let (null_bvar : index -> term) =
  fun i ->
    Tm_BVar
      {
        bv_index = i;
        bv_ppname = FStar_Reflection_Typing.pp_name_default;
        bv_range = FStar_Range.range_0
      }
let (gen_uvar : term -> (term, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Syntax.fsti" (Prims.of_int (151))
         (Prims.of_int (10)) (Prims.of_int (151)) (Prims.of_int (22)))
      (FStar_Range.mk_range "Pulse.Syntax.fsti" (Prims.of_int (151))
         (Prims.of_int (2)) (Prims.of_int (151)) (Prims.of_int (22)))
      (Obj.magic (FStar_Tactics_Builtins.fresh ()))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> Tm_UVar uu___))
let rec (eq_tm : term -> term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (Tm_VProp, Tm_VProp) -> true
      | (Tm_Emp, Tm_Emp) -> true
      | (Tm_Inames, Tm_Inames) -> true
      | (Tm_EmpInames, Tm_EmpInames) -> true
      | (Tm_Unknown, Tm_Unknown) -> true
      | (Tm_BVar x1, Tm_BVar x2) -> x1.bv_index = x2.bv_index
      | (Tm_Var x1, Tm_Var x2) -> x1.nm_index = x2.nm_index
      | (Tm_FVar x1, Tm_FVar x2) -> x1.fv_name = x2.fv_name
      | (Tm_UInst (x1, us1), Tm_UInst (x2, us2)) ->
          (x1.fv_name = x2.fv_name) && (us1 = us2)
      | (Tm_Constant c1, Tm_Constant c2) -> c1 = c2
      | (Tm_Refine (b1, t11), Tm_Refine (b2, t21)) ->
          (eq_tm b1.binder_ty b2.binder_ty) && (eq_tm t11 t21)
      | (Tm_PureApp (h1, o1, t11), Tm_PureApp (h2, o2, t21)) ->
          ((eq_tm h1 h2) && (o1 = o2)) && (eq_tm t11 t21)
      | (Tm_Star (l1, r1), Tm_Star (l2, r2)) ->
          (eq_tm l1 l2) && (eq_tm r1 r2)
      | (Tm_Pure p1, Tm_Pure p2) -> eq_tm p1 p2
      | (Tm_Type u1, Tm_Type u2) -> u1 = u2
      | (Tm_Let (t11, e1, e1'), Tm_Let (t21, e2, e2')) ->
          ((eq_tm t11 t21) && (eq_tm e1 e2)) && (eq_tm e1' e2')
      | (Tm_ExistsSL (u1, t11, b1, uu___), Tm_ExistsSL (u2, t21, b2, uu___1))
          -> ((u1 = u2) && (eq_tm t11 t21)) && (eq_tm b1 b2)
      | (Tm_ForallSL (u1, t11, b1), Tm_ForallSL (u2, t21, b2)) ->
          ((u1 = u2) && (eq_tm t11 t21)) && (eq_tm b1 b2)
      | (Tm_Arrow (b1, q1, c1), Tm_Arrow (b2, q2, c2)) ->
          ((eq_tm b1.binder_ty b2.binder_ty) && (q1 = q2)) && (eq_comp c1 c2)
      | (Tm_UVar z1, Tm_UVar z2) -> z1 = z2
      | (Tm_FStar t11, Tm_FStar t21) ->
          FStar_Reflection_Builtins.term_eq t11 t21
      | uu___ -> false
and (eq_comp : comp -> comp -> Prims.bool) =
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
and (eq_st_comp : st_comp -> st_comp -> Prims.bool) =
  fun s1 ->
    fun s2 ->
      (((s1.u = s2.u) && (eq_tm s1.res s2.res)) && (eq_tm s1.pre s2.pre)) &&
        (eq_tm s1.post s2.post)
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
      match (t1, t2) with
      | (Tm_Return (c1, use_eq1, t11), Tm_Return (c2, use_eq2, t21)) ->
          ((c1 = c2) && (use_eq1 = use_eq2)) && (eq_tm t11 t21)
      | (Tm_Abs (b1, o1, p1, t11, q1), Tm_Abs (b2, o2, p2, t21, q2)) ->
          ((((eq_tm b1.binder_ty b2.binder_ty) && (o1 = o2)) &&
              (eq_tm_opt p1 p2))
             && (eq_st_term t11 t21))
            && (eq_tm_opt q1 q2)
      | (Tm_STApp (h1, o1, t11), Tm_STApp (h2, o2, t21)) ->
          ((eq_tm h1 h2) && (o1 = o2)) && (eq_tm t11 t21)
      | (Tm_Bind (b1, t11, k1), Tm_Bind (b2, t21, k2)) ->
          ((eq_tm b1.binder_ty b2.binder_ty) && (eq_st_term t11 t21)) &&
            (eq_st_term k1 k2)
      | (Tm_IntroExists (b1, p1, l1), Tm_IntroExists (b2, p2, l2)) ->
          ((b1 = b2) && (eq_tm p1 p2)) && (eq_tm_list l1 l2)
      | (Tm_ElimExists p1, Tm_ElimExists p2) -> eq_tm p1 p2
      | (Tm_If (g1, ethen1, eelse1, p1), Tm_If (g2, ethen2, eelse2, p2)) ->
          (((eq_tm g1 g2) && (eq_st_term ethen1 ethen2)) &&
             (eq_st_term eelse1 eelse2))
            && (eq_tm_opt p1 p2)
      | (Tm_While (inv1, cond1, body1), Tm_While (inv2, cond2, body2)) ->
          ((eq_tm inv1 inv2) && (eq_st_term cond1 cond2)) &&
            (eq_st_term body1 body2)
      | (Tm_Par (preL1, eL1, postL1, preR1, eR1, postR1), Tm_Par
         (preL2, eL2, postL2, preR2, eR2, postR2)) ->
          (((((eq_tm preL1 preL2) && (eq_st_term eL1 eL2)) &&
               (eq_tm postL1 postL2))
              && (eq_tm preR1 preR2))
             && (eq_st_term eR1 eR2))
            && (eq_tm postR1 postR2)
      | (Tm_WithLocal (e1, e2), Tm_WithLocal (e3, e4)) ->
          (eq_tm e1 e3) && (eq_st_term e2 e4)
      | (Tm_Rewrite (e1, e2), Tm_Rewrite (e3, e4)) ->
          (eq_tm e1 e3) && (eq_tm e2 e4)
      | (Tm_Admit (c1, u1, t11, post1), Tm_Admit (c2, u2, t21, post2)) ->
          (((c1 = c2) && (u1 = u2)) && (eq_tm t11 t21)) &&
            (eq_tm_opt post1 post2)
      | (Tm_Protect t11, Tm_Protect t21) -> eq_st_term t11 t21
      | uu___ -> false
let rec (leftmost_head_and_args :
  term ->
    (term * (qualifier FStar_Pervasives_Native.option * term) Prims.list))
  =
  fun t ->
    match t with
    | Tm_PureApp (hd, q, arg) ->
        let uu___ = leftmost_head_and_args hd in
        (match uu___ with
         | (hd1, args) -> (hd1, (FStar_List_Tot_Base.op_At args [(q, arg)])))
    | uu___ -> (t, [])
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
let (comp_pre : comp -> term) =
  fun c ->
    match c with
    | C_ST s -> s.pre
    | C_STAtomic (uu___, s) -> s.pre
    | C_STGhost (uu___, s) -> s.pre
let (comp_post : comp -> term) =
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
let (term_of_nvar : nvar -> term) =
  fun x ->
    Tm_Var
      {
        nm_index = (FStar_Pervasives_Native.snd x);
        nm_ppname = (FStar_Pervasives_Native.fst x);
        nm_range = FStar_Range.range_0
      }
let (term_of_no_name_var : var -> term) = fun x -> term_of_nvar (v_as_nv x)
let (equiv_abs :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.typ ->
          FStar_Reflection_Data.aqualv ->
            var ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun e1 -> fun e2 -> fun ty -> fun q -> fun x -> fun eq -> Prims.admit ()
let (equiv_arrow :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.typ ->
          FStar_Reflection_Data.aqualv ->
            var ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun e1 -> fun e2 -> fun ty -> fun q -> fun x -> fun eq -> Prims.admit ()
let (equiv_abs_close :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.typ ->
          FStar_Reflection_Data.aqualv ->
            var ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun e1 -> fun e2 -> fun ty -> fun q -> fun x -> fun eq -> Prims.admit ()