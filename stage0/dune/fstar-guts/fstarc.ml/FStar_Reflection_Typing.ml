open Prims
let rec fold_left_dec : 'a 'b . 'a -> 'b Prims.list -> ('a -> 'b -> 'a) -> 'a
  =
  fun acc l f ->
    match l with | [] -> acc | x::xs -> fold_left_dec (f acc x) xs f
let rec map_dec : 'a 'b . 'a Prims.list -> ('a -> 'b) -> 'b Prims.list =
  fun l f -> match l with | [] -> [] | x::xs -> (f x) :: (map_dec xs f)
type pp_name_t = (Prims.string, Obj.t) FStar_Sealed_Inhabited.sealed
let pp_name_default : pp_name_t= FStar_Sealed_Inhabited.seal "x" "x"
let seal_pp_name (x : Prims.string) : pp_name_t=
  FStar_Sealed_Inhabited.seal "x" x
let tun : FStarC_Reflection_Types.term=
  FStarC_Reflection_V2_Builtins.pack_ln FStarC_Reflection_V2_Data.Tv_Unknown
type sort_t =
  (FStarC_Reflection_Types.term, Obj.t) FStar_Sealed_Inhabited.sealed
let sort_default : sort_t= FStar_Sealed_Inhabited.seal tun tun
let seal_sort (x : FStarC_Reflection_Types.term) : sort_t=
  FStar_Sealed_Inhabited.seal tun x
let mk_binder (pp_name : pp_name_t) (ty : FStarC_Reflection_Types.term)
  (q : FStarC_Reflection_V2_Data.aqualv) : FStarC_Reflection_Types.binder=
  FStarC_Reflection_V2_Builtins.pack_binder
    {
      FStarC_Reflection_V2_Data.sort2 = ty;
      FStarC_Reflection_V2_Data.qual = q;
      FStarC_Reflection_V2_Data.attrs = [];
      FStarC_Reflection_V2_Data.ppname2 = pp_name
    }
let mk_simple_binder (pp_name : pp_name_t)
  (ty : FStarC_Reflection_Types.term) :
  FStarC_Reflection_V2_Data.simple_binder=
  FStarC_Reflection_V2_Builtins.pack_binder
    {
      FStarC_Reflection_V2_Data.sort2 = ty;
      FStarC_Reflection_V2_Data.qual = FStarC_Reflection_V2_Data.Q_Explicit;
      FStarC_Reflection_V2_Data.attrs = [];
      FStarC_Reflection_V2_Data.ppname2 = pp_name
    }
let extend_env (e : FStarC_Reflection_Types.env)
  (x : FStarC_Reflection_V2_Data.var) (ty : FStarC_Reflection_Types.term) :
  FStarC_Reflection_Types.env=
  FStar_Reflection_V2_Derived.push_binding e
    {
      FStarC_Reflection_V2_Data.uniq1 = x;
      FStarC_Reflection_V2_Data.sort3 = ty;
      FStarC_Reflection_V2_Data.ppname3 = (seal_pp_name "x")
    }
let bv_index (x : FStarC_Reflection_Types.bv) :
  FStarC_Reflection_V2_Data.var=
  (FStarC_Reflection_V2_Builtins.inspect_bv x).FStarC_Reflection_V2_Data.index
let namedv_uniq (x : FStarC_Reflection_Types.namedv) :
  FStarC_Reflection_V2_Data.var=
  (FStarC_Reflection_V2_Builtins.inspect_namedv x).FStarC_Reflection_V2_Data.uniq
let binder_sort (b : FStarC_Reflection_Types.binder) :
  FStarC_Reflection_Types.typ=
  (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2
let binder_qual (b : FStarC_Reflection_Types.binder) :
  FStarC_Reflection_V2_Data.aqualv=
  let uu___ = FStarC_Reflection_V2_Builtins.inspect_binder b in
  match uu___ with
  | { FStarC_Reflection_V2_Data.sort2 = uu___1;
      FStarC_Reflection_V2_Data.qual = q;
      FStarC_Reflection_V2_Data.attrs = uu___2;
      FStarC_Reflection_V2_Data.ppname2 = uu___3;_} -> q
type subst_elt =
  | DT of Prims.nat * FStarC_Reflection_Types.term 
  | NT of FStarC_Reflection_V2_Data.var * FStarC_Reflection_Types.term 
  | ND of FStarC_Reflection_V2_Data.var * Prims.nat 
let uu___is_DT (projectee : subst_elt) : Prims.bool=
  match projectee with | DT (_0, _1) -> true | uu___ -> false
let __proj__DT__item___0 (projectee : subst_elt) : Prims.nat=
  match projectee with | DT (_0, _1) -> _0
let __proj__DT__item___1 (projectee : subst_elt) :
  FStarC_Reflection_Types.term= match projectee with | DT (_0, _1) -> _1
let uu___is_NT (projectee : subst_elt) : Prims.bool=
  match projectee with | NT (_0, _1) -> true | uu___ -> false
let __proj__NT__item___0 (projectee : subst_elt) :
  FStarC_Reflection_V2_Data.var= match projectee with | NT (_0, _1) -> _0
let __proj__NT__item___1 (projectee : subst_elt) :
  FStarC_Reflection_Types.term= match projectee with | NT (_0, _1) -> _1
let uu___is_ND (projectee : subst_elt) : Prims.bool=
  match projectee with | ND (_0, _1) -> true | uu___ -> false
let __proj__ND__item___0 (projectee : subst_elt) :
  FStarC_Reflection_V2_Data.var= match projectee with | ND (_0, _1) -> _0
let __proj__ND__item___1 (projectee : subst_elt) : Prims.nat=
  match projectee with | ND (_0, _1) -> _1
let shift_subst_elt (n : Prims.nat) (uu___ : subst_elt) : subst_elt=
  match uu___ with
  | DT (i, t) -> DT ((i + n), t)
  | NT (x, t) -> NT (x, t)
  | ND (x, i) -> ND (x, (i + n))
type subst = subst_elt Prims.list
let shift_subst_n (n : Prims.nat) :
  subst_elt Prims.list -> subst_elt Prims.list=
  FStar_List_Tot_Base.map (shift_subst_elt n)
let shift_subst : subst_elt Prims.list -> subst_elt Prims.list=
  shift_subst_n Prims.int_one
let maybe_uniq_of_term (x : FStarC_Reflection_Types.term) :
  FStarC_Reflection_V2_Data.var FStar_Pervasives_Native.option=
  match FStarC_Reflection_V2_Builtins.inspect_ln x with
  | FStarC_Reflection_V2_Data.Tv_Var namedv ->
      FStar_Pervasives_Native.Some (namedv_uniq namedv)
  | uu___ -> FStar_Pervasives_Native.None
let rec find_matching_subst_elt_bv (s : subst)
  (bv : FStarC_Reflection_Types.bv) :
  subst_elt FStar_Pervasives_Native.option=
  match s with
  | [] -> FStar_Pervasives_Native.None
  | (DT (j, t))::ss ->
      if j = (bv_index bv)
      then FStar_Pervasives_Native.Some (DT (j, t))
      else find_matching_subst_elt_bv ss bv
  | uu___::ss -> find_matching_subst_elt_bv ss bv
let subst_db (bv : FStarC_Reflection_Types.bv) (s : subst) :
  FStarC_Reflection_Types.term=
  match find_matching_subst_elt_bv s bv with
  | FStar_Pervasives_Native.Some (DT (uu___, t)) ->
      (match maybe_uniq_of_term t with
       | FStar_Pervasives_Native.None -> t
       | FStar_Pervasives_Native.Some k ->
           let v =
             FStarC_Reflection_V2_Builtins.pack_namedv
               {
                 FStarC_Reflection_V2_Data.uniq = k;
                 FStarC_Reflection_V2_Data.sort =
                   ((FStarC_Reflection_V2_Builtins.inspect_bv bv).FStarC_Reflection_V2_Data.sort1);
                 FStarC_Reflection_V2_Data.ppname =
                   ((FStarC_Reflection_V2_Builtins.inspect_bv bv).FStarC_Reflection_V2_Data.ppname1)
               } in
           FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_Var v))
  | uu___ ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_BVar bv)
let rec find_matching_subst_elt_var (s : subst)
  (v : FStarC_Reflection_Types.namedv) :
  subst_elt FStar_Pervasives_Native.option=
  match s with
  | [] -> FStar_Pervasives_Native.None
  | (NT (y, uu___))::rest ->
      if y = (namedv_uniq v)
      then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.hd s)
      else find_matching_subst_elt_var rest v
  | (ND (y, uu___))::rest ->
      if y = (namedv_uniq v)
      then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.hd s)
      else find_matching_subst_elt_var rest v
  | uu___::rest -> find_matching_subst_elt_var rest v
let subst_var (v : FStarC_Reflection_Types.namedv) (s : subst) :
  FStarC_Reflection_Types.term=
  match find_matching_subst_elt_var s v with
  | FStar_Pervasives_Native.Some (NT (uu___, t)) ->
      (match maybe_uniq_of_term t with
       | FStar_Pervasives_Native.None -> t
       | FStar_Pervasives_Native.Some k ->
           FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_Var
                (FStarC_Reflection_V2_Builtins.pack_namedv
                   (let uu___1 =
                      FStarC_Reflection_V2_Builtins.inspect_namedv v in
                    {
                      FStarC_Reflection_V2_Data.uniq = k;
                      FStarC_Reflection_V2_Data.sort =
                        (uu___1.FStarC_Reflection_V2_Data.sort);
                      FStarC_Reflection_V2_Data.ppname =
                        (uu___1.FStarC_Reflection_V2_Data.ppname)
                    }))))
  | FStar_Pervasives_Native.Some (ND (uu___, i)) ->
      let bv =
        FStarC_Reflection_V2_Builtins.pack_bv
          {
            FStarC_Reflection_V2_Data.index = i;
            FStarC_Reflection_V2_Data.sort1 =
              ((FStarC_Reflection_V2_Builtins.inspect_namedv v).FStarC_Reflection_V2_Data.sort);
            FStarC_Reflection_V2_Data.ppname1 =
              ((FStarC_Reflection_V2_Builtins.inspect_namedv v).FStarC_Reflection_V2_Data.ppname)
          } in
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_BVar bv)
  | uu___ ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_Var v)
let make_bv (n : Prims.nat) : FStarC_Reflection_V2_Data.bv_view=
  {
    FStarC_Reflection_V2_Data.index = n;
    FStarC_Reflection_V2_Data.sort1 = sort_default;
    FStarC_Reflection_V2_Data.ppname1 = pp_name_default
  }
let make_bv_with_name (s : pp_name_t) (n : Prims.nat) :
  FStarC_Reflection_V2_Data.bv_view=
  {
    FStarC_Reflection_V2_Data.index = n;
    FStarC_Reflection_V2_Data.sort1 = sort_default;
    FStarC_Reflection_V2_Data.ppname1 = s
  }
let var_as_bv (v : Prims.nat) : FStarC_Reflection_Types.bv=
  FStarC_Reflection_V2_Builtins.pack_bv (make_bv v)
let make_namedv (n : Prims.nat) : FStarC_Reflection_V2_Data.namedv_view=
  {
    FStarC_Reflection_V2_Data.uniq = n;
    FStarC_Reflection_V2_Data.sort = sort_default;
    FStarC_Reflection_V2_Data.ppname = pp_name_default
  }
let make_namedv_with_name (s : pp_name_t) (n : Prims.nat) :
  FStarC_Reflection_V2_Data.namedv_view=
  {
    FStarC_Reflection_V2_Data.uniq = n;
    FStarC_Reflection_V2_Data.sort = sort_default;
    FStarC_Reflection_V2_Data.ppname = s
  }
let var_as_namedv (v : Prims.nat) : FStarC_Reflection_Types.namedv=
  FStarC_Reflection_V2_Builtins.pack_namedv
    {
      FStarC_Reflection_V2_Data.uniq = v;
      FStarC_Reflection_V2_Data.sort = sort_default;
      FStarC_Reflection_V2_Data.ppname = pp_name_default
    }
let binder_of_t_q (t : FStarC_Reflection_Types.term)
  (q : FStarC_Reflection_V2_Data.aqualv) : FStarC_Reflection_Types.binder=
  mk_binder pp_name_default t q
let mk_total_tm (t : FStarC_Reflection_Types.term) :
  FStarC_Reflection_Types.comp=
  FStarC_Reflection_V2_Builtins.pack_comp
    (FStarC_Reflection_V2_Data.C_Total t)
let open_with_var_elt (x : FStarC_Reflection_V2_Data.var) (i : Prims.nat) :
  subst_elt=
  DT
    (i,
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_Var (var_as_namedv x))))
let open_with_var (x : FStarC_Reflection_V2_Data.var) (i : Prims.nat) :
  subst= [open_with_var_elt x i]
let rec binder_offset_patterns
  (ps : (FStarC_Reflection_V2_Data.pattern * Prims.bool) Prims.list) :
  Prims.nat=
  match ps with
  | [] -> Prims.int_zero
  | (p, b)::ps1 ->
      let n = binder_offset_pattern p in
      let m = binder_offset_patterns ps1 in n + m
and binder_offset_pattern (p : FStarC_Reflection_V2_Data.pattern) :
  Prims.nat=
  match p with
  | FStarC_Reflection_V2_Data.Pat_Constant uu___ -> Prims.int_zero
  | FStarC_Reflection_V2_Data.Pat_Dot_Term uu___ -> Prims.int_zero
  | FStarC_Reflection_V2_Data.Pat_Var (uu___, uu___1) -> Prims.int_one
  | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
      binder_offset_patterns subpats
let open_with (t : FStarC_Reflection_Types.term)
  (v : FStarC_Reflection_Types.term) : FStarC_Reflection_Types.term=
  FStar_Reflection_Typing_Builtins.open_with t v
let open_term (t : FStarC_Reflection_Types.term)
  (v : FStarC_Reflection_V2_Data.var) : FStarC_Reflection_Types.term=
  FStar_Reflection_Typing_Builtins.open_term t v
let close_term (t : FStarC_Reflection_Types.term)
  (v : FStarC_Reflection_V2_Data.var) : FStarC_Reflection_Types.term=
  FStar_Reflection_Typing_Builtins.close_term t v
let rename (t : FStarC_Reflection_Types.term)
  (x : FStarC_Reflection_V2_Data.var) (y : FStarC_Reflection_V2_Data.var) :
  FStarC_Reflection_Types.term= FStar_Reflection_Typing_Builtins.rename t x y
let unit_fv : FStarC_Reflection_Types.fv=
  FStarC_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.unit_lid
let bool_fv : FStarC_Reflection_Types.fv=
  FStarC_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.bool_lid
let eqtype_lid : FStarC_Reflection_Types.name= ["Prims"; "eqtype"]
let u_zero : FStarC_Reflection_Types.universe=
  FStarC_Reflection_V2_Builtins.pack_universe
    FStarC_Reflection_V2_Data.Uv_Zero
let tm_type_tm (u : FStarC_Reflection_Types.universe) :
  FStarC_Reflection_Types.term=
  FStarC_Reflection_V2_Builtins.pack_ln (FStarC_Reflection_V2_Data.Tv_Type u)
let bool_ty_tm : FStarC_Reflection_Types.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar bool_fv)
let true_bool_tm : FStarC_Reflection_Types.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_True)
let false_bool_tm : FStarC_Reflection_Types.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_False)
let eq2 (u : FStarC_Reflection_Types.universe)
  (t : FStarC_Reflection_Types.term) (v0 : FStarC_Reflection_Types.term)
  (v1 : FStarC_Reflection_Types.term) : FStarC_Reflection_Types.term=
  let eq21 =
    FStarC_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.eq2_qn in
  let eq22 =
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_UInst (eq21, [u])) in
  let h =
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_App
         (eq22, (t, FStarC_Reflection_V2_Data.Q_Implicit))) in
  let h1 =
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_App
         (h, (v0, FStarC_Reflection_V2_Data.Q_Explicit))) in
  let h2 =
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_App
         (h1, (v1, FStarC_Reflection_V2_Data.Q_Explicit))) in
  h2
let b2t_lid : FStarC_Reflection_Types.name= ["Prims"; "b2t"]
let b2t_fv : FStarC_Reflection_Types.fv=
  FStarC_Reflection_V2_Builtins.pack_fv b2t_lid
let b2t_ty : FStarC_Reflection_Types.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Arrow
       ((mk_binder (FStar_Sealed.seal "x") bool_ty_tm
           FStarC_Reflection_V2_Data.Q_Explicit),
         (mk_total_tm (tm_type_tm u_zero))))
type term_ctxt =
  | Ctxt_hole 
  | Ctxt_app_head of term_ctxt * (unit * unit) 
  | Ctxt_app_arg of unit * unit * term_ctxt 
let uu___is_Ctxt_hole uu___ =
  match uu___ with | Ctxt_hole _ -> true | _ -> false
let uu___is_Ctxt_app_head uu___ =
  match uu___ with | Ctxt_app_head _ -> true | _ -> false
let uu___is_Ctxt_app_arg uu___ =
  match uu___ with | Ctxt_app_arg _ -> true | _ -> false
type ('dummyV0, 'dummyV1) constant_typing =
  | CT_Unit 
  | CT_True 
  | CT_False 
let uu___is_CT_Unit (uu___ : FStarC_Reflection_V2_Data.vconst)
  (uu___1 : unit) (projectee : (Obj.t, Obj.t) constant_typing) : Prims.bool=
  match Obj.magic projectee with | CT_Unit -> true | uu___2 -> false
let uu___is_CT_True (uu___ : FStarC_Reflection_V2_Data.vconst)
  (uu___1 : unit) (projectee : (Obj.t, Obj.t) constant_typing) : Prims.bool=
  match Obj.magic projectee with | CT_True -> true | uu___2 -> false
let uu___is_CT_False (uu___ : FStarC_Reflection_V2_Data.vconst)
  (uu___1 : unit) (projectee : (Obj.t, Obj.t) constant_typing) : Prims.bool=
  match Obj.magic projectee with | CT_False -> true | uu___2 -> false
type ('dummyV0, 'dummyV1) univ_eq =
  | UN_Refl of unit 
  | UN_MaxCongL of unit * unit * unit * (Obj.t, Obj.t) univ_eq 
  | UN_MaxCongR of unit * unit * unit * (Obj.t, Obj.t) univ_eq 
  | UN_MaxComm of unit * unit 
  | UN_MaxLeq of unit * unit * (Obj.t, Obj.t) univ_leq 
and ('dummyV0, 'dummyV1) univ_leq =
  | UNLEQ_Refl of unit 
  | UNLEQ_Succ of unit * unit * (Obj.t, Obj.t) univ_leq 
  | UNLEQ_Max of unit * unit 
let uu___is_UN_Refl uu___1 uu___ uu___2 =
  match uu___2 with | UN_Refl _ -> true | _ -> false
let uu___is_UN_MaxCongL uu___1 uu___ uu___2 =
  match uu___2 with | UN_MaxCongL _ -> true | _ -> false
let uu___is_UN_MaxCongR uu___1 uu___ uu___2 =
  match uu___2 with | UN_MaxCongR _ -> true | _ -> false
let uu___is_UN_MaxComm uu___1 uu___ uu___2 =
  match uu___2 with | UN_MaxComm _ -> true | _ -> false
let uu___is_UN_MaxLeq uu___1 uu___ uu___2 =
  match uu___2 with | UN_MaxLeq _ -> true | _ -> false
let uu___is_UNLEQ_Refl uu___1 uu___ uu___2 =
  match uu___2 with | UNLEQ_Refl _ -> true | _ -> false
let uu___is_UNLEQ_Succ uu___1 uu___ uu___2 =
  match uu___2 with | UNLEQ_Succ _ -> true | _ -> false
let uu___is_UNLEQ_Max uu___1 uu___ uu___2 =
  match uu___2 with | UNLEQ_Max _ -> true | _ -> false
let mk_if (scrutinee : FStarC_Reflection_Types.term)
  (then_ : FStarC_Reflection_Types.term)
  (else_ : FStarC_Reflection_Types.term) : FStarC_Reflection_Types.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Match
       (scrutinee, FStar_Pervasives_Native.None,
         [((FStarC_Reflection_V2_Data.Pat_Constant
              FStarC_Reflection_V2_Data.C_True), then_);
         ((FStarC_Reflection_V2_Data.Pat_Constant
             FStarC_Reflection_V2_Data.C_False), else_)]))
type comp_typ =
  (FStarC_TypeChecker_Core.tot_or_ghost * FStarC_Reflection_Types.typ)
let close_comp_typ' (c : FStarC_Tactics_Types_Reflection.comp_spec_typ)
  (x : FStarC_Reflection_V2_Data.var) (i : Prims.nat) :
  (FStarC_TypeChecker_Core.tot_or_ghost * unit)=
  ((FStar_Pervasives_Native.fst c), ())
let close_comp_typ (c : FStarC_Tactics_Types_Reflection.comp_spec_typ)
  (x : FStarC_Reflection_V2_Data.var) :
  (FStarC_TypeChecker_Core.tot_or_ghost * unit)=
  close_comp_typ' c x Prims.int_zero
let open_comp_typ' (c : FStarC_Tactics_Types_Reflection.comp_spec_typ)
  (x : FStarC_Reflection_V2_Data.var) (i : Prims.nat) :
  (FStarC_TypeChecker_Core.tot_or_ghost * unit)=
  ((FStar_Pervasives_Native.fst c), ())
let open_comp_typ (c : FStarC_Tactics_Types_Reflection.comp_spec_typ)
  (x : FStarC_Reflection_V2_Data.var) :
  (FStarC_TypeChecker_Core.tot_or_ghost * unit)=
  open_comp_typ' c x Prims.int_zero
type relation =
  | R_Eq 
  | R_Sub 
let uu___is_R_Eq (projectee : relation) : Prims.bool=
  match projectee with | R_Eq -> true | uu___ -> false
let uu___is_R_Sub (projectee : relation) : Prims.bool=
  match projectee with | R_Sub -> true | uu___ -> false
type binding = (FStarC_Reflection_V2_Data.var * FStarC_Reflection_Types.term)
type bindings = binding Prims.list
let rename_bindings (bs : ('uuuuu * FStarC_Reflection_Types.term) Prims.list)
  (x : FStarC_Reflection_V2_Data.var) (y : FStarC_Reflection_V2_Data.var) :
  ('uuuuu * FStarC_Reflection_Types.term) Prims.list=
  FStar_List_Tot_Base.map
    (fun uu___ -> match uu___ with | (v, t) -> (v, (rename t x y))) bs
let rec extend_env_l (g : FStarC_Reflection_Types.env) (bs : bindings) :
  FStarC_Reflection_Types.env=
  match bs with
  | [] -> g
  | (x, t)::bs1 -> extend_env (extend_env_l g bs1) x t
let is_non_informative_name (l : FStarC_Reflection_Types.name) : Prims.bool=
  ((l = FStar_Reflection_Const.unit_lid) ||
     (l = FStar_Reflection_Const.squash_qn))
    || (l = ["FStar"; "Ghost"; "erased"])
let is_non_informative_fv (f : FStarC_Reflection_Types.fv) : Prims.bool=
  is_non_informative_name (FStarC_Reflection_V2_Builtins.inspect_fv f)
let bindings_to_refl_bindings (bs : binding Prims.list) :
  FStarC_Reflection_V2_Data.binding Prims.list=
  FStar_List_Tot_Base.map
    (fun uu___ ->
       match uu___ with
       | (v, ty) ->
           {
             FStarC_Reflection_V2_Data.uniq1 = v;
             FStarC_Reflection_V2_Data.sort3 = ty;
             FStarC_Reflection_V2_Data.ppname3 = pp_name_default
           }) bs
let refl_bindings_to_bindings
  (bs : FStarC_Reflection_V2_Data.binding Prims.list) : binding Prims.list=
  FStar_List_Tot_Base.map
    (fun b ->
       ((b.FStarC_Reflection_V2_Data.uniq1),
         (b.FStarC_Reflection_V2_Data.sort3))) bs
type ('dummyV0, 'dummyV1) non_informative =
  | Non_informative_type of FStarC_Reflection_Types.env * unit 
  | Non_informative_fv of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.fv 
  | Non_informative_uinst of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.fv * unit Prims.list 
  | Non_informative_app of FStarC_Reflection_Types.env * unit * unit * unit *
  (Obj.t, Obj.t) non_informative 
  | Non_informative_total_arrow of FStarC_Reflection_Types.env * unit * unit
  * unit * (Obj.t, Obj.t) non_informative 
  | Non_informative_ghost_arrow of FStarC_Reflection_Types.env * unit * unit
  * unit 
  | Non_informative_token of FStarC_Reflection_Types.env * unit * unit 
let uu___is_Non_informative_type uu___1 uu___ uu___2 =
  match uu___2 with | Non_informative_type _ -> true | _ -> false
let uu___is_Non_informative_fv uu___1 uu___ uu___2 =
  match uu___2 with | Non_informative_fv _ -> true | _ -> false
let uu___is_Non_informative_uinst uu___1 uu___ uu___2 =
  match uu___2 with | Non_informative_uinst _ -> true | _ -> false
let uu___is_Non_informative_app uu___1 uu___ uu___2 =
  match uu___2 with | Non_informative_app _ -> true | _ -> false
let uu___is_Non_informative_total_arrow uu___1 uu___ uu___2 =
  match uu___2 with | Non_informative_total_arrow _ -> true | _ -> false
let uu___is_Non_informative_ghost_arrow uu___1 uu___ uu___2 =
  match uu___2 with | Non_informative_ghost_arrow _ -> true | _ -> false
let uu___is_Non_informative_token uu___1 uu___ uu___2 =
  match uu___2 with | Non_informative_token _ -> true | _ -> false
let binding_to_namedv (b : FStarC_Reflection_V2_Data.binding) :
  FStarC_Reflection_Types.namedv=
  FStarC_Reflection_V2_Builtins.pack_namedv
    {
      FStarC_Reflection_V2_Data.uniq = (b.FStarC_Reflection_V2_Data.uniq1);
      FStarC_Reflection_V2_Data.sort =
        (FStar_Sealed.seal b.FStarC_Reflection_V2_Data.sort3);
      FStarC_Reflection_V2_Data.ppname =
        (b.FStarC_Reflection_V2_Data.ppname3)
    }
let rec elaborate_pat (p : FStarC_Reflection_V2_Data.pattern)
  (bs : FStarC_Reflection_V2_Data.binding Prims.list) :
  (FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.binding
    Prims.list) FStar_Pervasives_Native.option=
  match (p, bs) with
  | (FStarC_Reflection_V2_Data.Pat_Constant c, uu___) ->
      FStar_Pervasives_Native.Some
        ((FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Const c)), bs)
  | (FStarC_Reflection_V2_Data.Pat_Cons (fv, univs, subpats), bs1) ->
      let head =
        match univs with
        | FStar_Pervasives_Native.Some univs1 ->
            FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_UInst (fv, univs1))
        | FStar_Pervasives_Native.None ->
            FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar fv) in
      fold_left_dec (FStar_Pervasives_Native.Some (head, bs1)) subpats
        (fun st pi ->
           let uu___ = pi in
           match uu___ with
           | (p1, i) ->
               (match st with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (head1, bs2) ->
                    (match elaborate_pat p1 bs2 with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (t, bs') ->
                         FStar_Pervasives_Native.Some
                           ((FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_App
                                  (head1,
                                    (t,
                                      (if i
                                       then
                                         FStarC_Reflection_V2_Data.Q_Implicit
                                       else
                                         FStarC_Reflection_V2_Data.Q_Explicit))))),
                             bs'))))
  | (FStarC_Reflection_V2_Data.Pat_Var (uu___, uu___1), b::bs1) ->
      FStar_Pervasives_Native.Some
        ((FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Var (binding_to_namedv b))), bs1)
  | (FStarC_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.Some t),
     uu___) -> FStar_Pervasives_Native.Some (t, bs)
  | (FStarC_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.None),
     uu___) -> FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
type ('dummyV0, 'dummyV1, 'dummyV2) typing =
  | T_Token of FStarC_Reflection_Types.env * unit *
  FStarC_Tactics_Types_Reflection.comp_spec_typ * unit 
  | T_Var of FStarC_Reflection_Types.env * FStarC_Reflection_Types.namedv 
  | T_FVar of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv 
  | T_UInst of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv *
  FStarC_Reflection_Types.universe Prims.list 
  | T_Const of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.vconst
  * unit * (Obj.t, Obj.t) constant_typing 
  | T_Abs of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  FStarC_Reflection_Types.term * unit *
  FStarC_Tactics_Types_Reflection.comp_spec_typ * unit * unit *
  FStarC_TypeChecker_Core.tot_or_ghost * (Obj.t, Obj.t, Obj.t) typing *
  (Obj.t, Obj.t, Obj.t) typing 
  | T_App of FStarC_Reflection_Types.env * unit * unit * unit * unit *
  FStarC_TypeChecker_Core.tot_or_ghost * (Obj.t, Obj.t, Obj.t) typing *
  (Obj.t, Obj.t, Obj.t) typing 
  | T_Let of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  unit * FStarC_Reflection_Types.typ * unit * unit *
  FStarC_TypeChecker_Core.tot_or_ghost * (Obj.t, Obj.t, Obj.t) typing *
  (Obj.t, Obj.t, Obj.t) typing 
  | T_Arrow of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  FStarC_Reflection_Types.term * unit * unit * unit * unit *
  FStarC_TypeChecker_Core.tot_or_ghost * FStarC_TypeChecker_Core.tot_or_ghost
  * FStarC_TypeChecker_Core.tot_or_ghost * (Obj.t, Obj.t, Obj.t) typing *
  (Obj.t, Obj.t, Obj.t) typing 
  | T_Refine of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  FStarC_Reflection_Types.term * unit * unit * unit *
  FStarC_TypeChecker_Core.tot_or_ghost * FStarC_TypeChecker_Core.tot_or_ghost
  * (Obj.t, Obj.t, Obj.t) typing * (Obj.t, Obj.t, Obj.t) typing 
  | T_PropIrrelevance of FStarC_Reflection_Types.env * unit * unit *
  FStarC_TypeChecker_Core.tot_or_ghost * FStarC_TypeChecker_Core.tot_or_ghost
  * (Obj.t, Obj.t, Obj.t) typing * (Obj.t, Obj.t, Obj.t) typing 
  | T_Sub of FStarC_Reflection_Types.env * unit *
  FStarC_Tactics_Types_Reflection.comp_spec_typ *
  FStarC_Tactics_Types_Reflection.comp_spec_typ * (Obj.t, Obj.t, Obj.t)
  typing * (Obj.t, Obj.t, Obj.t, Obj.t) related_comp 
  | T_If of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * unit * FStarC_Reflection_V2_Data.var *
  FStarC_TypeChecker_Core.tot_or_ghost * FStarC_TypeChecker_Core.tot_or_ghost
  * (Obj.t, Obj.t, Obj.t) typing * (Obj.t, Obj.t, Obj.t) typing * (Obj.t,
  Obj.t, Obj.t) typing * (Obj.t, Obj.t, Obj.t) typing 
  | T_Match of FStarC_Reflection_Types.env * FStarC_Reflection_Types.universe
  * FStarC_Reflection_Types.typ * FStarC_Reflection_Types.term *
  FStarC_TypeChecker_Core.tot_or_ghost * (Obj.t, Obj.t, Obj.t) typing *
  FStarC_TypeChecker_Core.tot_or_ghost * (Obj.t, Obj.t, Obj.t) typing * (unit
  * unit) Prims.list * FStarC_Tactics_Types_Reflection.comp_spec_typ *
  FStarC_Reflection_V2_Data.binding Prims.list Prims.list * (Obj.t, Obj.t,
  Obj.t, Obj.t, Obj.t) match_is_complete * (Obj.t, Obj.t, Obj.t, Obj.t,
  Obj.t, Obj.t, Obj.t) branches_typing 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3) related =
  | Rel_refl of FStarC_Reflection_Types.env * unit * relation 
  | Rel_sym of FStarC_Reflection_Types.env * unit * unit * (Obj.t, Obj.t,
  Obj.t, Obj.t) related 
  | Rel_trans of FStarC_Reflection_Types.env * unit * unit * unit * relation
  * (Obj.t, Obj.t, Obj.t, Obj.t) related * (Obj.t, Obj.t, Obj.t, Obj.t)
  related 
  | Rel_univ of FStarC_Reflection_Types.env * unit * unit * (Obj.t, Obj.t)
  univ_eq 
  | Rel_beta of FStarC_Reflection_Types.env * unit * unit * unit * unit 
  | Rel_eq_token of FStarC_Reflection_Types.env * unit * unit * unit 
  | Rel_subtyping_token of FStarC_Reflection_Types.env * unit * unit * unit 
  | Rel_equiv of FStarC_Reflection_Types.env * unit * unit * relation *
  (Obj.t, Obj.t, Obj.t, Obj.t) related 
  | Rel_arrow of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * unit *
  FStarC_Tactics_Types_Reflection.comp_spec_typ *
  FStarC_Tactics_Types_Reflection.comp_spec_typ * relation *
  FStarC_Reflection_V2_Data.var * (Obj.t, Obj.t, Obj.t, Obj.t) related *
  (Obj.t, Obj.t, Obj.t, Obj.t) related_comp 
  | Rel_abs of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * unit * unit * unit *
  FStarC_Reflection_V2_Data.var * (Obj.t, Obj.t, Obj.t, Obj.t) related *
  (Obj.t, Obj.t, Obj.t, Obj.t) related 
  | Rel_ctxt of FStarC_Reflection_Types.env * unit * unit * term_ctxt *
  (Obj.t, Obj.t, Obj.t, Obj.t) related 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3) related_comp =
  | Relc_typ of FStarC_Reflection_Types.env * unit * unit *
  FStarC_TypeChecker_Core.tot_or_ghost * relation * (Obj.t, Obj.t, Obj.t,
  Obj.t) related 
  | Relc_total_ghost of FStarC_Reflection_Types.env * unit 
  | Relc_ghost_total of FStarC_Reflection_Types.env * unit * (Obj.t, 
  Obj.t) non_informative 
and ('g, 'scuu, 'scuty, 'sc, 'rty, 'dummyV0, 'dummyV1) branches_typing =
  | BT_Nil 
  | BT_S of (unit * unit) * FStarC_Reflection_V2_Data.binding Prims.list *
  ('g, 'scuu, 'scuty, 'sc, 'rty, Obj.t, Obj.t) branch_typing * (unit * unit)
  Prims.list * FStarC_Reflection_V2_Data.binding Prims.list Prims.list * (
  'g, 'scuu, 'scuty, 'sc, 'rty, Obj.t, Obj.t) branches_typing 
and ('g, 'scuu, 'scuty, 'sc, 'rty, 'dummyV0, 'dummyV1) branch_typing =
  | BO of FStarC_Reflection_V2_Data.pattern *
  FStarC_Reflection_V2_Data.binding Prims.list *
  FStarC_Reflection_V2_Data.var * unit * unit * (Obj.t, Obj.t, 'rty) typing 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3, 'dummyV4) match_is_complete =
  | MC_Tok of FStarC_Reflection_Types.env * unit * unit * unit Prims.list *
  FStarC_Reflection_V2_Data.binding Prims.list Prims.list * unit 
let uu___is_T_Token uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Token _ -> true | _ -> false
let uu___is_T_Var uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Var _ -> true | _ -> false
let uu___is_T_FVar uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_FVar _ -> true | _ -> false
let uu___is_T_UInst uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_UInst _ -> true | _ -> false
let uu___is_T_Const uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Const _ -> true | _ -> false
let uu___is_T_Abs uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Abs _ -> true | _ -> false
let uu___is_T_App uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_App _ -> true | _ -> false
let uu___is_T_Let uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Let _ -> true | _ -> false
let uu___is_T_Arrow uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Arrow _ -> true | _ -> false
let uu___is_T_Refine uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Refine _ -> true | _ -> false
let uu___is_T_PropIrrelevance uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_PropIrrelevance _ -> true | _ -> false
let uu___is_T_Sub uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Sub _ -> true | _ -> false
let uu___is_T_If uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_If _ -> true | _ -> false
let uu___is_T_Match uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Match _ -> true | _ -> false
let uu___is_Rel_refl uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_refl _ -> true | _ -> false
let uu___is_Rel_sym uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_sym _ -> true | _ -> false
let uu___is_Rel_trans uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_trans _ -> true | _ -> false
let uu___is_Rel_univ uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_univ _ -> true | _ -> false
let uu___is_Rel_beta uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_beta _ -> true | _ -> false
let uu___is_Rel_eq_token uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_eq_token _ -> true | _ -> false
let uu___is_Rel_subtyping_token uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_subtyping_token _ -> true | _ -> false
let uu___is_Rel_equiv uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_equiv _ -> true | _ -> false
let uu___is_Rel_arrow uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_arrow _ -> true | _ -> false
let uu___is_Rel_abs uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_abs _ -> true | _ -> false
let uu___is_Rel_ctxt uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Rel_ctxt _ -> true | _ -> false
let uu___is_Relc_typ uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Relc_typ _ -> true | _ -> false
let uu___is_Relc_total_ghost uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Relc_total_ghost _ -> true | _ -> false
let uu___is_Relc_ghost_total uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Relc_ghost_total _ -> true | _ -> false
let uu___is_BT_Nil uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___7 =
  match uu___7 with | BT_Nil _ -> true | _ -> false
let uu___is_BT_S uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___7 =
  match uu___7 with | BT_S _ -> true | _ -> false
let uu___is_BO uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___7 =
  match uu___7 with | BO _ -> true | _ -> false
let uu___is_MC_Tok uu___4 uu___3 uu___2 uu___1 uu___ uu___5 =
  match uu___5 with | MC_Tok _ -> true | _ -> false
type ('g, 't1, 't2) sub_typing = ('g, 't1, Obj.t, 't2) related
type ('g, 'c1, 'c2) sub_comp = ('g, 'c1, Obj.t, 'c2) related_comp
type ('g, 't1, 't2) equiv = ('g, 't1, Obj.t, 't2) related
type ('g, 'e, 't) tot_typing = ('g, 'e, Obj.t) typing
type ('g, 'e, 't) ghost_typing = ('g, 'e, Obj.t) typing
let simplify_umax (g : FStarC_Reflection_Types.env) (t : unit) (u : unit)
  (d : (Obj.t, Obj.t, Obj.t) typing) : (Obj.t, Obj.t, Obj.t) typing=
  let ue = UN_MaxLeq ((), (), (UNLEQ_Refl ())) in
  let du = Rel_univ (g, (), (), (Obj.magic ue)) in
  let du1 = Obj.magic (Rel_equiv (g, (), (), R_Sub, (Obj.magic du))) in
  T_Sub
    (g, (), (FStarC_TypeChecker_Core.E_Total, ()),
      (FStarC_TypeChecker_Core.E_Total, ()), d,
      (Relc_typ
         (g, (), (), FStarC_TypeChecker_Core.E_Total, R_Sub, (Obj.magic du1))))
type fstar_env = FStarC_Reflection_Types.env
type fstar_top_env = fstar_env
type ('dummyV0, 'dummyV1) sigelt_typing =
  | ST_Let of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv *
  FStarC_Reflection_Types.univ_name Prims.list * FStarC_Reflection_Types.typ
  * FStarC_Reflection_Types.term * unit 
  | ST_Let_Opaque of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv
  * FStarC_Reflection_Types.univ_name Prims.list *
  FStarC_Reflection_Types.typ * unit 
let uu___is_ST_Let (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : Prims.bool=
  match projectee with
  | ST_Let (g, fv, us, ty, tm, _5) -> true
  | uu___2 -> false
let __proj__ST_Let__item__g (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : FStarC_Reflection_Types.env=
  match projectee with | ST_Let (g, fv, us, ty, tm, _5) -> g
let __proj__ST_Let__item__fv (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : FStarC_Reflection_Types.fv=
  match projectee with | ST_Let (g, fv, us, ty, tm, _5) -> fv
let __proj__ST_Let__item__us (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) :
  FStarC_Reflection_Types.univ_name Prims.list=
  match projectee with | ST_Let (g, fv, us, ty, tm, _5) -> us
let __proj__ST_Let__item__ty (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : FStarC_Reflection_Types.typ=
  match projectee with | ST_Let (g, fv, us, ty, tm, _5) -> ty
let __proj__ST_Let__item__tm (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : FStarC_Reflection_Types.term=
  match projectee with | ST_Let (g, fv, us, ty, tm, _5) -> tm
let uu___is_ST_Let_Opaque (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : Prims.bool=
  match projectee with
  | ST_Let_Opaque (g, fv, us, ty, _4) -> true
  | uu___2 -> false
let __proj__ST_Let_Opaque__item__g (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : FStarC_Reflection_Types.env=
  match projectee with | ST_Let_Opaque (g, fv, us, ty, _4) -> g
let __proj__ST_Let_Opaque__item__fv (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : FStarC_Reflection_Types.fv=
  match projectee with | ST_Let_Opaque (g, fv, us, ty, _4) -> fv
let __proj__ST_Let_Opaque__item__us (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) :
  FStarC_Reflection_Types.univ_name Prims.list=
  match projectee with | ST_Let_Opaque (g, fv, us, ty, _4) -> us
let __proj__ST_Let_Opaque__item__ty (uu___ : FStarC_Reflection_Types.env)
  (uu___1 : FStarC_Reflection_Types.sigelt)
  (projectee : (Obj.t, Obj.t) sigelt_typing) : FStarC_Reflection_Types.typ=
  match projectee with | ST_Let_Opaque (g, fv, us, ty, _4) -> ty
type blob = (Prims.string * FStarC_Reflection_Types.term)
type ('g, 't) sigelt_for =
  (Prims.bool * FStarC_Reflection_Types.sigelt * blob
    FStar_Pervasives_Native.option)
type ('g, 't) dsl_tac_result_t =
  (('g, Obj.t) sigelt_for Prims.list * ('g, 't) sigelt_for * ('g, Obj.t)
    sigelt_for Prims.list)
type dsl_tac_t =
  (fstar_top_env * FStarC_Reflection_Types.typ
    FStar_Pervasives_Native.option) ->
    ((Obj.t, Obj.t) dsl_tac_result_t, Obj.t) FStar_Tactics_Effect.tac_repr
let mkif (uu___12 : fstar_env) (uu___11 : FStarC_Reflection_Types.term)
  (uu___10 : FStarC_Reflection_Types.term)
  (uu___9 : FStarC_Reflection_Types.term)
  (uu___8 : FStarC_Reflection_Types.term) (uu___7 : unit)
  (uu___6 : FStarC_Reflection_V2_Data.var)
  (uu___5 : FStarC_TypeChecker_Core.tot_or_ghost)
  (uu___4 : FStarC_TypeChecker_Core.tot_or_ghost)
  (uu___3 : (Obj.t, Obj.t, Obj.t) typing)
  (uu___2 : (Obj.t, Obj.t, Obj.t) typing)
  (uu___1 : (Obj.t, Obj.t, Obj.t) typing)
  (uu___ : (Obj.t, Obj.t, Obj.t) typing) : (Obj.t, Obj.t, Obj.t) typing=
  (fun g scrutinee then_ else_ ty u_ty hyp eff ty_eff ts tt te tr ->
     let brt = ((), ()) in
     let bre = ((), ()) in
     let brty uu___ =
       BT_S
         (brt, [],
           (BO
              ((FStarC_Reflection_V2_Data.Pat_Constant
                  FStarC_Reflection_V2_Data.C_True), [], hyp, (), (), tt)),
           [bre], [[]],
           (BT_S
              (bre, [],
                (BO
                   ((FStarC_Reflection_V2_Data.Pat_Constant
                       FStarC_Reflection_V2_Data.C_False), [], hyp, (), (),
                     te)), [], [], BT_Nil))) in
     Obj.magic
       (T_Match
          (g, u_zero, bool_ty_tm, scrutinee, FStarC_TypeChecker_Core.E_Total,
            (Obj.magic (T_FVar (g, bool_fv))), eff, ts, [brt; bre],
            (eff, ()), [[]; []],
            (MC_Tok (g, (), (), [(); ()], [[]; []], ())), (brty ()))))
    uu___12 uu___11 uu___10 uu___9 uu___8 uu___7 uu___6 uu___5 uu___4 uu___3
    uu___2 uu___1 uu___
let mk_checked_let (g : FStarC_Reflection_Types.env)
  (cur_module : FStarC_Reflection_Types.name) (nm : Prims.string)
  (tm : FStarC_Reflection_Types.term) (ty : FStarC_Reflection_Types.typ) :
  (Obj.t, Obj.t) sigelt_for=
  let fv =
    FStarC_Reflection_V2_Builtins.pack_fv
      (FStar_List_Tot_Base.op_At cur_module [nm]) in
  let lb =
    FStarC_Reflection_V2_Builtins.pack_lb
      {
        FStarC_Reflection_V2_Data.lb_fv = fv;
        FStarC_Reflection_V2_Data.lb_us = [];
        FStarC_Reflection_V2_Data.lb_typ = ty;
        FStarC_Reflection_V2_Data.lb_def = tm
      } in
  let se =
    FStarC_Reflection_V2_Builtins.pack_sigelt
      (FStarC_Reflection_V2_Data.Sg_Let (false, [lb])) in
  (true, se, FStar_Pervasives_Native.None)
let mk_unchecked_let (g : FStarC_Reflection_Types.env)
  (cur_module : FStarC_Reflection_Types.name) (nm : Prims.string)
  (tm : FStarC_Reflection_Types.term) (ty : FStarC_Reflection_Types.typ) :
  (Prims.bool * FStarC_Reflection_Types.sigelt * blob
    FStar_Pervasives_Native.option)=
  let fv =
    FStarC_Reflection_V2_Builtins.pack_fv
      (FStar_List_Tot_Base.op_At cur_module [nm]) in
  let lb =
    FStarC_Reflection_V2_Builtins.pack_lb
      {
        FStarC_Reflection_V2_Data.lb_fv = fv;
        FStarC_Reflection_V2_Data.lb_us = [];
        FStarC_Reflection_V2_Data.lb_typ = ty;
        FStarC_Reflection_V2_Data.lb_def = tm
      } in
  let se =
    FStarC_Reflection_V2_Builtins.pack_sigelt
      (FStarC_Reflection_V2_Data.Sg_Let (false, [lb])) in
  (false, se, FStar_Pervasives_Native.None)
