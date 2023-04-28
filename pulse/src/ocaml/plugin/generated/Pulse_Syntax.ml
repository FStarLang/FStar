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
type bv = {
  bv_index: index ;
  bv_ppname: ppname }
let (__proj__Mkbv__item__bv_index : bv -> index) =
  fun projectee ->
    match projectee with | { bv_index; bv_ppname;_} -> bv_index
let (__proj__Mkbv__item__bv_ppname : bv -> ppname) =
  fun projectee ->
    match projectee with | { bv_index; bv_ppname;_} -> bv_ppname
type nm = {
  nm_index: var ;
  nm_ppname: ppname }
let (__proj__Mknm__item__nm_index : nm -> var) =
  fun projectee ->
    match projectee with | { nm_index; nm_ppname;_} -> nm_index
let (__proj__Mknm__item__nm_ppname : nm -> ppname) =
  fun projectee ->
    match projectee with | { nm_index; nm_ppname;_} -> nm_ppname
type qualifier =
  | Implicit 
let (uu___is_Implicit : qualifier -> Prims.bool) = fun projectee -> true
type should_elim_t = (Prims.bool, unit) FStar_Sealed_Inhabited.sealed
let (should_elim_true : should_elim_t) =
  FStar_Sealed_Inhabited.seal false true
let (should_elim_false : should_elim_t) =
  FStar_Sealed_Inhabited.seal false false
type term =
  | Tm_BVar of bv 
  | Tm_Var of nm 
  | Tm_FVar of FStar_Reflection_Types.name 
  | Tm_UInst of FStar_Reflection_Types.name * universe Prims.list 
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
  | Tm_Bind of st_term * st_term 
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
let rec (freevars : term -> var FStar_Set.set) =
  fun t ->
    match t with
    | Tm_BVar uu___ -> FStar_Set.empty ()
    | Tm_FVar uu___ -> FStar_Set.empty ()
    | Tm_UInst (uu___, uu___1) -> FStar_Set.empty ()
    | Tm_Constant uu___ -> FStar_Set.empty ()
    | Tm_Emp -> FStar_Set.empty ()
    | Tm_Type uu___ -> FStar_Set.empty ()
    | Tm_VProp -> FStar_Set.empty ()
    | Tm_Inames -> FStar_Set.empty ()
    | Tm_EmpInames -> FStar_Set.empty ()
    | Tm_UVar uu___ -> FStar_Set.empty ()
    | Tm_Unknown -> FStar_Set.empty ()
    | Tm_Var nm1 -> FStar_Set.singleton nm1.nm_index
    | Tm_Refine (b, body) ->
        FStar_Set.union (freevars b.binder_ty) (freevars body)
    | Tm_PureApp (t1, uu___, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Tm_Star (t1, t2) -> FStar_Set.union (freevars t1) (freevars t2)
    | Tm_ExistsSL (uu___, t1, t2, uu___1) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Tm_ForallSL (uu___, t1, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Tm_Let (t1, e1, e2) ->
        FStar_Set.union (FStar_Set.union (freevars t1) (freevars e1))
          (freevars e2)
    | Tm_Pure p -> freevars p
    | Tm_Arrow (b, uu___, body) ->
        FStar_Set.union (freevars b.binder_ty) (freevars_comp body)
and (freevars_comp : comp -> var FStar_Set.set) =
  fun c ->
    match c with
    | C_Tot t -> freevars t
    | C_ST s -> freevars_st_comp s
    | C_STAtomic (inames, s) ->
        FStar_Set.union (freevars inames) (freevars_st_comp s)
    | C_STGhost (inames, s) ->
        FStar_Set.union (freevars inames) (freevars_st_comp s)
and (freevars_st_comp : st_comp -> var FStar_Set.set) =
  fun s ->
    FStar_Set.union (FStar_Set.union (freevars s.res) (freevars s.pre))
      (freevars s.post)
let (freevars_opt : term FStar_Pervasives_Native.option -> var FStar_Set.set)
  =
  fun t ->
    match t with
    | FStar_Pervasives_Native.None -> FStar_Set.empty ()
    | FStar_Pervasives_Native.Some t1 -> freevars t1
let rec (freevars_list : term Prims.list -> var FStar_Set.set) =
  fun t ->
    match t with
    | [] -> FStar_Set.empty ()
    | hd::tl -> FStar_Set.union (freevars hd) (freevars_list tl)
let rec (freevars_st : st_term -> var FStar_Set.set) =
  fun t ->
    match t with
    | Tm_Return (uu___, uu___1, t1) -> freevars t1
    | Tm_Abs (b, uu___, pre_hint, body, post_hint) ->
        FStar_Set.union (freevars b.binder_ty)
          (FStar_Set.union (freevars_st body)
             (FStar_Set.union (freevars_opt pre_hint)
                (freevars_opt post_hint)))
    | Tm_STApp (t1, uu___, t2) -> FStar_Set.union (freevars t1) (freevars t2)
    | Tm_Bind (t1, t2) -> FStar_Set.union (freevars_st t1) (freevars_st t2)
    | Tm_If (t1, e1, e2, post) ->
        FStar_Set.union (FStar_Set.union (freevars t1) (freevars_st e1))
          (FStar_Set.union (freevars_st e2) (freevars_opt post))
    | Tm_ElimExists p -> freevars p
    | Tm_IntroExists (uu___, e, p) ->
        FStar_Set.union (freevars e) (freevars_list p)
    | Tm_While (inv, cond, body) ->
        FStar_Set.union (freevars inv)
          (FStar_Set.union (freevars_st cond) (freevars_st body))
    | Tm_Par (preL, eL, postL, preR, eR, postR) ->
        FStar_Set.union
          (FStar_Set.union (freevars preL)
             (FStar_Set.union (freevars_st eL) (freevars postL)))
          (FStar_Set.union (freevars preR)
             (FStar_Set.union (freevars_st eR) (freevars postR)))
    | Tm_WithLocal (t1, t2) -> FStar_Set.union (freevars t1) (freevars_st t2)
    | Tm_Rewrite (t1, t2) -> FStar_Set.union (freevars t1) (freevars t2)
    | Tm_Admit (uu___, uu___1, t1, post) ->
        FStar_Set.union (freevars t1) (freevars_opt post)
    | Tm_Protect t1 -> freevars_st t1
let rec (ln' : term -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with
      | Tm_BVar { bv_index = j; bv_ppname = uu___;_} -> j <= i
      | Tm_Var uu___ -> true
      | Tm_FVar uu___ -> true
      | Tm_UInst (uu___, uu___1) -> true
      | Tm_Constant uu___ -> true
      | Tm_Emp -> true
      | Tm_Type uu___ -> true
      | Tm_VProp -> true
      | Tm_Inames -> true
      | Tm_EmpInames -> true
      | Tm_UVar uu___ -> true
      | Tm_Unknown -> true
      | Tm_Refine (b, phi) ->
          (ln' b.binder_ty i) && (ln' phi (i + Prims.int_one))
      | Tm_PureApp (t1, uu___, t2) -> (ln' t1 i) && (ln' t2 i)
      | Tm_Star (t1, t2) -> (ln' t1 i) && (ln' t2 i)
      | Tm_Let (t1, e1, e2) ->
          ((ln' t1 i) && (ln' e1 i)) && (ln' e2 (i + Prims.int_one))
      | Tm_Pure p -> ln' p i
      | Tm_ExistsSL (uu___, t1, body, uu___1) ->
          (ln' t1 i) && (ln' body (i + Prims.int_one))
      | Tm_ForallSL (uu___, t1, body) ->
          (ln' t1 i) && (ln' body (i + Prims.int_one))
      | Tm_Arrow (b, uu___, c) ->
          (ln' b.binder_ty i) && (ln_c' c (i + Prims.int_one))
and (ln_c' : comp -> Prims.int -> Prims.bool) =
  fun c ->
    fun i ->
      match c with
      | C_Tot t -> ln' t i
      | C_ST s -> ln_st_comp s i
      | C_STAtomic (inames, s) -> (ln' inames i) && (ln_st_comp s i)
      | C_STGhost (inames, s) -> (ln' inames i) && (ln_st_comp s i)
and (ln_st_comp : st_comp -> Prims.int -> Prims.bool) =
  fun s ->
    fun i ->
      ((ln' s.res i) && (ln' s.pre i)) && (ln' s.post (i + Prims.int_one))
let (ln_opt' :
  term FStar_Pervasives_Native.option -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some t1 -> ln' t1 i
let rec (ln_list' : term Prims.list -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with | [] -> true | hd::tl -> (ln' hd i) && (ln_list' tl i)
let rec (ln_st' : st_term -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with
      | Tm_Return (uu___, uu___1, t1) -> ln' t1 i
      | Tm_Abs (b, uu___, pre_hint, body, post) ->
          (((ln' b.binder_ty i) && (ln_st' body (i + Prims.int_one))) &&
             (ln_opt' pre_hint (i + Prims.int_one)))
            && (ln_opt' post (i + (Prims.of_int (2))))
      | Tm_STApp (t1, uu___, t2) -> (ln' t1 i) && (ln' t2 i)
      | Tm_Bind (t1, t2) -> (ln_st' t1 i) && (ln_st' t2 (i + Prims.int_one))
      | Tm_If (b, then_, else_, post) ->
          (((ln' b i) && (ln_st' then_ i)) && (ln_st' else_ i)) &&
            (ln_opt' post (i + Prims.int_one))
      | Tm_ElimExists p -> ln' p i
      | Tm_IntroExists (uu___, p, e) -> (ln' p i) && (ln_list' e i)
      | Tm_While (inv, cond, body) ->
          ((ln' inv (i + Prims.int_one)) && (ln_st' cond i)) &&
            (ln_st' body i)
      | Tm_Par (preL, eL, postL, preR, eR, postR) ->
          (((((ln' preL i) && (ln_st' eL i)) &&
               (ln' postL (i + Prims.int_one)))
              && (ln' preR i))
             && (ln_st' eR i))
            && (ln' postR (i + Prims.int_one))
      | Tm_WithLocal (t1, t2) ->
          (ln' t1 i) && (ln_st' t2 (i + Prims.int_one))
      | Tm_Rewrite (t1, t2) -> (ln' t1 i) && (ln' t2 i)
      | Tm_Admit (uu___, uu___1, t1, post) ->
          (ln' t1 i) && (ln_opt' post (i + Prims.int_one))
      | Tm_Protect t1 -> ln_st' t1 i
let (ln : term -> Prims.bool) = fun t -> ln' t (Prims.of_int (-1))
let (ln_st : st_term -> Prims.bool) = fun t -> ln_st' t (Prims.of_int (-1))
let (ln_c : comp -> Prims.bool) = fun c -> ln_c' c (Prims.of_int (-1))
let rec (open_term' : term -> term -> index -> term) =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Tm_BVar bv1 -> if i = bv1.bv_index then v else t
        | Tm_Var uu___ -> t
        | Tm_FVar uu___ -> t
        | Tm_UInst (uu___, uu___1) -> t
        | Tm_Constant uu___ -> t
        | Tm_Type uu___ -> t
        | Tm_VProp -> t
        | Tm_Emp -> t
        | Tm_Inames -> t
        | Tm_EmpInames -> t
        | Tm_UVar uu___ -> t
        | Tm_Unknown -> t
        | Tm_Refine (b, phi) ->
            Tm_Refine
              ({
                 binder_ty = (open_term' b.binder_ty v i);
                 binder_ppname = (b.binder_ppname)
               }, (open_term' phi v (i + Prims.int_one)))
        | Tm_PureApp (head, q, arg) ->
            Tm_PureApp ((open_term' head v i), q, (open_term' arg v i))
        | Tm_Let (t1, e1, e2) ->
            Tm_Let
              ((open_term' t1 v i), (open_term' e1 v i),
                (open_term' e2 v (i + Prims.int_one)))
        | Tm_Pure p -> Tm_Pure (open_term' p v i)
        | Tm_Star (l, r) -> Tm_Star ((open_term' l v i), (open_term' r v i))
        | Tm_ExistsSL (u, t1, body, se) ->
            Tm_ExistsSL
              (u, (open_term' t1 v i),
                (open_term' body v (i + Prims.int_one)), se)
        | Tm_ForallSL (u, t1, body) ->
            Tm_ForallSL
              (u, (open_term' t1 v i),
                (open_term' body v (i + Prims.int_one)))
        | Tm_Arrow (b, q, c) ->
            Tm_Arrow
              ({
                 binder_ty = (open_term' b.binder_ty v i);
                 binder_ppname = (b.binder_ppname)
               }, q, (open_comp' c v (i + Prims.int_one)))
and (open_comp' : comp -> term -> index -> comp) =
  fun c ->
    fun v ->
      fun i ->
        match c with
        | C_Tot t -> C_Tot (open_term' t v i)
        | C_ST s -> C_ST (open_st_comp' s v i)
        | C_STAtomic (inames, s) ->
            C_STAtomic ((open_term' inames v i), (open_st_comp' s v i))
        | C_STGhost (inames, s) ->
            C_STGhost ((open_term' inames v i), (open_st_comp' s v i))
and (open_st_comp' : st_comp -> term -> index -> st_comp) =
  fun s ->
    fun v ->
      fun i ->
        {
          u = (s.u);
          res = (open_term' s.res v i);
          pre = (open_term' s.pre v i);
          post = (open_term' s.post v (i + Prims.int_one))
        }
let (open_term_opt' :
  term FStar_Pervasives_Native.option ->
    term -> index -> term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t1 ->
            FStar_Pervasives_Native.Some (open_term' t1 v i)
let rec (open_term_list' :
  term Prims.list -> term -> index -> term Prims.list) =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | [] -> []
        | hd::tl -> (open_term' hd v i) :: (open_term_list' tl v i)
let rec (open_st_term' : st_term -> term -> index -> st_term) =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Tm_Return (c, use_eq, t1) ->
            Tm_Return (c, use_eq, (open_term' t1 v i))
        | Tm_Abs (b, q, pre_hint, body, post) ->
            Tm_Abs
              ({
                 binder_ty = (open_term' b.binder_ty v i);
                 binder_ppname = (b.binder_ppname)
               }, q, (open_term_opt' pre_hint v (i + Prims.int_one)),
                (open_st_term' body v (i + Prims.int_one)),
                (open_term_opt' post v (i + (Prims.of_int (2)))))
        | Tm_STApp (head, q, arg) ->
            Tm_STApp ((open_term' head v i), q, (open_term' arg v i))
        | Tm_Bind (e1, e2) ->
            Tm_Bind
              ((open_st_term' e1 v i),
                (open_st_term' e2 v (i + Prims.int_one)))
        | Tm_If (b, then_, else_, post) ->
            Tm_If
              ((open_term' b v i), (open_st_term' then_ v i),
                (open_st_term' else_ v i),
                (open_term_opt' post v (i + Prims.int_one)))
        | Tm_ElimExists p -> Tm_ElimExists (open_term' p v i)
        | Tm_IntroExists (b, p, e) ->
            Tm_IntroExists (b, (open_term' p v i), (open_term_list' e v i))
        | Tm_While (inv, cond, body) ->
            Tm_While
              ((open_term' inv v (i + Prims.int_one)),
                (open_st_term' cond v i), (open_st_term' body v i))
        | Tm_Par (preL, eL, postL, preR, eR, postR) ->
            Tm_Par
              ((open_term' preL v i), (open_st_term' eL v i),
                (open_term' postL v (i + Prims.int_one)),
                (open_term' preR v i), (open_st_term' eR v i),
                (open_term' postR v (i + Prims.int_one)))
        | Tm_WithLocal (e1, e2) ->
            Tm_WithLocal
              ((open_term' e1 v i), (open_st_term' e2 v (i + Prims.int_one)))
        | Tm_Rewrite (e1, e2) ->
            Tm_Rewrite ((open_term' e1 v i), (open_term' e2 v i))
        | Tm_Admit (c, u, t1, post) ->
            Tm_Admit
              (c, u, (open_term' t1 v i),
                (open_term_opt' post v (i + Prims.int_one)))
        | Tm_Protect t1 -> Tm_Protect (open_st_term' t1 v i)
let (open_term : term -> var -> term) =
  fun t ->
    fun v ->
      open_term' t
        (Tm_Var
           {
             nm_index = v;
             nm_ppname = FStar_Reflection_Typing.pp_name_default
           }) Prims.int_zero
let (open_st_term : st_term -> var -> st_term) =
  fun t ->
    fun v ->
      open_st_term' t
        (Tm_Var
           {
             nm_index = v;
             nm_ppname = FStar_Reflection_Typing.pp_name_default
           }) Prims.int_zero
let (open_comp_with : comp -> term -> comp) =
  fun c -> fun x -> open_comp' c x Prims.int_zero
let rec (close_term' : term -> var -> index -> term) =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Tm_Var nm1 ->
            if nm1.nm_index = v
            then Tm_BVar { bv_index = i; bv_ppname = (nm1.nm_ppname) }
            else t
        | Tm_BVar uu___ -> t
        | Tm_FVar uu___ -> t
        | Tm_UInst (uu___, uu___1) -> t
        | Tm_Constant uu___ -> t
        | Tm_Type uu___ -> t
        | Tm_VProp -> t
        | Tm_Emp -> t
        | Tm_Inames -> t
        | Tm_EmpInames -> t
        | Tm_UVar uu___ -> t
        | Tm_Unknown -> t
        | Tm_Refine (b, phi) ->
            Tm_Refine
              ({
                 binder_ty = (close_term' b.binder_ty v i);
                 binder_ppname = (b.binder_ppname)
               }, (close_term' phi v (i + Prims.int_one)))
        | Tm_PureApp (head, q, arg) ->
            Tm_PureApp ((close_term' head v i), q, (close_term' arg v i))
        | Tm_Let (t1, e1, e2) ->
            Tm_Let
              ((close_term' t1 v i), (close_term' e1 v i),
                (close_term' e2 v (i + Prims.int_one)))
        | Tm_Pure p -> Tm_Pure (close_term' p v i)
        | Tm_Star (l, r) ->
            Tm_Star ((close_term' l v i), (close_term' r v i))
        | Tm_ExistsSL (u, t1, body, se) ->
            Tm_ExistsSL
              (u, (close_term' t1 v i),
                (close_term' body v (i + Prims.int_one)), se)
        | Tm_ForallSL (u, t1, body) ->
            Tm_ForallSL
              (u, (close_term' t1 v i),
                (close_term' body v (i + Prims.int_one)))
        | Tm_Arrow (b, q, c) ->
            Tm_Arrow
              ({
                 binder_ty = (close_term' b.binder_ty v i);
                 binder_ppname = (b.binder_ppname)
               }, q, (close_comp' c v (i + Prims.int_one)))
and (close_comp' : comp -> var -> index -> comp) =
  fun c ->
    fun v ->
      fun i ->
        match c with
        | C_Tot t -> C_Tot (close_term' t v i)
        | C_ST s -> C_ST (close_st_comp' s v i)
        | C_STAtomic (inames, s) ->
            C_STAtomic ((close_term' inames v i), (close_st_comp' s v i))
        | C_STGhost (inames, s) ->
            C_STGhost ((close_term' inames v i), (close_st_comp' s v i))
and (close_st_comp' : st_comp -> var -> index -> st_comp) =
  fun s ->
    fun v ->
      fun i ->
        {
          u = (s.u);
          res = (close_term' s.res v i);
          pre = (close_term' s.pre v i);
          post = (close_term' s.post v (i + Prims.int_one))
        }
let (close_term_opt' :
  term FStar_Pervasives_Native.option ->
    var -> index -> term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t1 ->
            FStar_Pervasives_Native.Some (close_term' t1 v i)
let rec (close_term_list' :
  term Prims.list -> var -> index -> term Prims.list) =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | [] -> []
        | hd::tl -> (close_term' hd v i) :: (close_term_list' tl v i)
let rec (close_st_term' : st_term -> var -> index -> st_term) =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Tm_Return (c, use_eq, t1) ->
            Tm_Return (c, use_eq, (close_term' t1 v i))
        | Tm_Abs (b, q, pre_hint, body, post) ->
            Tm_Abs
              ({
                 binder_ty = (close_term' b.binder_ty v i);
                 binder_ppname = (b.binder_ppname)
               }, q, (close_term_opt' pre_hint v (i + Prims.int_one)),
                (close_st_term' body v (i + Prims.int_one)),
                (close_term_opt' post v (i + (Prims.of_int (2)))))
        | Tm_STApp (head, q, arg) ->
            Tm_STApp ((close_term' head v i), q, (close_term' arg v i))
        | Tm_Bind (e1, e2) ->
            Tm_Bind
              ((close_st_term' e1 v i),
                (close_st_term' e2 v (i + Prims.int_one)))
        | Tm_If (b, then_, else_, post) ->
            Tm_If
              ((close_term' b v i), (close_st_term' then_ v i),
                (close_st_term' else_ v i),
                (close_term_opt' post v (i + Prims.int_one)))
        | Tm_ElimExists p -> Tm_ElimExists (close_term' p v i)
        | Tm_IntroExists (b, p, e) ->
            Tm_IntroExists (b, (close_term' p v i), (close_term_list' e v i))
        | Tm_While (inv, cond, body) ->
            Tm_While
              ((close_term' inv v (i + Prims.int_one)),
                (close_st_term' cond v i), (close_st_term' body v i))
        | Tm_Par (preL, eL, postL, preR, eR, postR) ->
            Tm_Par
              ((close_term' preL v i), (close_st_term' eL v i),
                (close_term' postL v (i + Prims.int_one)),
                (close_term' preR v i), (close_st_term' eR v i),
                (close_term' postR v (i + Prims.int_one)))
        | Tm_WithLocal (e1, e2) ->
            Tm_WithLocal
              ((close_term' e1 v i),
                (close_st_term' e2 v (i + Prims.int_one)))
        | Tm_Rewrite (e1, e2) ->
            Tm_Rewrite ((close_term' e1 v i), (close_term' e2 v i))
        | Tm_Admit (c, u, t1, post) ->
            Tm_Admit
              (c, u, (close_term' t1 v i),
                (close_term_opt' post v (i + Prims.int_one)))
        | Tm_Protect t1 -> Tm_Protect (close_st_term' t1 v i)
let (close_term : term -> var -> term) =
  fun t -> fun v -> close_term' t v Prims.int_zero
let (close_st_term : st_term -> var -> st_term) =
  fun t -> fun v -> close_st_term' t v Prims.int_zero
let (close_comp : comp -> var -> comp) =
  fun t -> fun v -> close_comp' t v Prims.int_zero
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
let (term_of_var : var -> term) =
  fun x ->
    Tm_Var
      { nm_index = x; nm_ppname = FStar_Reflection_Typing.pp_name_default }
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
let (mk_bvar : Prims.string -> index -> term) =
  fun s ->
    fun i ->
      Tm_BVar
        { bv_index = i; bv_ppname = (FStar_Reflection_Typing.seal_pp_name s)
        }
let (null_var : var -> term) =
  fun v ->
    Tm_Var
      { nm_index = v; nm_ppname = FStar_Reflection_Typing.pp_name_default }
let (null_bvar : index -> term) =
  fun i ->
    Tm_BVar
      { bv_index = i; bv_ppname = FStar_Reflection_Typing.pp_name_default }
let (gen_uvar : term -> (term, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Syntax.fsti" (Prims.of_int (745))
         (Prims.of_int (10)) (Prims.of_int (745)) (Prims.of_int (22)))
      (FStar_Range.mk_range "Pulse.Syntax.fsti" (Prims.of_int (745))
         (Prims.of_int (2)) (Prims.of_int (745)) (Prims.of_int (22)))
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
      | (Tm_FVar x1, Tm_FVar x2) -> x1 = x2
      | (Tm_UInst (x1, us1), Tm_UInst (x2, us2)) -> (x1 = x2) && (us1 = us2)
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
      | (Tm_Bind (t11, k1), Tm_Bind (t21, k2)) ->
          (eq_st_term t11 t21) && (eq_st_term k1 k2)
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