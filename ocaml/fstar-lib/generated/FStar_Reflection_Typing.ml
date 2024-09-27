open Prims
let rec fold_left_dec : 'a 'b . 'a -> 'b Prims.list -> ('a -> 'b -> 'a) -> 'a
  =
  fun acc ->
    fun l ->
      fun f ->
        match l with | [] -> acc | x::xs -> fold_left_dec (f acc x) xs f
let rec map_dec : 'a 'b . 'a Prims.list -> ('a -> 'b) -> 'b Prims.list =
  fun l ->
    fun f -> match l with | [] -> [] | x::xs -> (f x) :: (map_dec xs f)
type ('a, 'b, 'f, 'xs, 'ys) zip2prop = Obj.t
let (lookup_bvar :
  FStar_Reflection_Types.env ->
    Prims.int -> FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun e -> fun x -> Prims.magic ()
let (lookup_fvar_uinst :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.fv ->
      FStar_Reflection_Types.universe Prims.list ->
        FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun e -> fun x -> fun us -> Prims.magic ()
let (lookup_fvar :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.fv ->
      FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun e -> fun x -> lookup_fvar_uinst e x []
type pp_name_t = (Prims.string, unit) FStar_Sealed_Inhabited.sealed
let (pp_name_default : pp_name_t) = FStar_Sealed_Inhabited.seal "x" "x"
let (seal_pp_name : Prims.string -> pp_name_t) =
  fun x -> FStar_Sealed_Inhabited.seal "x" x
let (tun : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln FStar_Reflection_V2_Data.Tv_Unknown
type sort_t =
  (FStar_Reflection_Types.term, unit) FStar_Sealed_Inhabited.sealed
let (sort_default : sort_t) = FStar_Sealed_Inhabited.seal tun tun
let (seal_sort : FStar_Reflection_Types.term -> sort_t) =
  fun x -> FStar_Sealed_Inhabited.seal tun x
let (mk_binder :
  pp_name_t ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_V2_Data.aqualv -> FStar_Reflection_Types.binder)
  =
  fun pp_name ->
    fun ty ->
      fun q ->
        FStar_Reflection_V2_Builtins.pack_binder
          {
            FStar_Reflection_V2_Data.sort2 = ty;
            FStar_Reflection_V2_Data.qual = q;
            FStar_Reflection_V2_Data.attrs = [];
            FStar_Reflection_V2_Data.ppname2 = pp_name
          }
let (mk_simple_binder :
  pp_name_t ->
    FStar_Reflection_Types.term -> FStar_Reflection_V2_Data.simple_binder)
  =
  fun pp_name ->
    fun ty ->
      FStar_Reflection_V2_Builtins.pack_binder
        {
          FStar_Reflection_V2_Data.sort2 = ty;
          FStar_Reflection_V2_Data.qual = FStar_Reflection_V2_Data.Q_Explicit;
          FStar_Reflection_V2_Data.attrs = [];
          FStar_Reflection_V2_Data.ppname2 = pp_name
        }
let (extend_env :
  FStar_Reflection_Types.env ->
    FStar_Reflection_V2_Data.var ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.env)
  =
  fun e ->
    fun x ->
      fun ty ->
        FStar_Reflection_V2_Derived.push_binding e
          {
            FStar_Reflection_V2_Data.uniq1 = x;
            FStar_Reflection_V2_Data.sort3 = ty;
            FStar_Reflection_V2_Data.ppname3 = (seal_pp_name "x")
          }
let (bv_index : FStar_Reflection_Types.bv -> FStar_Reflection_V2_Data.var) =
  fun x ->
    (FStar_Reflection_V2_Builtins.inspect_bv x).FStar_Reflection_V2_Data.index
let (namedv_uniq :
  FStar_Reflection_Types.namedv -> FStar_Reflection_V2_Data.var) =
  fun x ->
    (FStar_Reflection_V2_Builtins.inspect_namedv x).FStar_Reflection_V2_Data.uniq
let (binder_sort :
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.typ) =
  fun b ->
    (FStar_Reflection_V2_Builtins.inspect_binder b).FStar_Reflection_V2_Data.sort2
let (binder_qual :
  FStar_Reflection_Types.binder -> FStar_Reflection_V2_Data.aqualv) =
  fun b ->
    let uu___ = FStar_Reflection_V2_Builtins.inspect_binder b in
    match uu___ with
    | { FStar_Reflection_V2_Data.sort2 = uu___1;
        FStar_Reflection_V2_Data.qual = q;
        FStar_Reflection_V2_Data.attrs = uu___2;
        FStar_Reflection_V2_Data.ppname2 = uu___3;_} -> q
type subst_elt =
  | DT of Prims.nat * FStar_Reflection_Types.term 
  | NT of FStar_Reflection_V2_Data.var * FStar_Reflection_Types.term 
  | ND of FStar_Reflection_V2_Data.var * Prims.nat 
let (uu___is_DT : subst_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | DT (_0, _1) -> true | uu___ -> false
let (__proj__DT__item___0 : subst_elt -> Prims.nat) =
  fun projectee -> match projectee with | DT (_0, _1) -> _0
let (__proj__DT__item___1 : subst_elt -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | DT (_0, _1) -> _1
let (uu___is_NT : subst_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | NT (_0, _1) -> true | uu___ -> false
let (__proj__NT__item___0 : subst_elt -> FStar_Reflection_V2_Data.var) =
  fun projectee -> match projectee with | NT (_0, _1) -> _0
let (__proj__NT__item___1 : subst_elt -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | NT (_0, _1) -> _1
let (uu___is_ND : subst_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | ND (_0, _1) -> true | uu___ -> false
let (__proj__ND__item___0 : subst_elt -> FStar_Reflection_V2_Data.var) =
  fun projectee -> match projectee with | ND (_0, _1) -> _0
let (__proj__ND__item___1 : subst_elt -> Prims.nat) =
  fun projectee -> match projectee with | ND (_0, _1) -> _1
let (shift_subst_elt : Prims.nat -> subst_elt -> subst_elt) =
  fun n ->
    fun uu___ ->
      match uu___ with
      | DT (i, t) -> DT ((i + n), t)
      | NT (x, t) -> NT (x, t)
      | ND (x, i) -> ND (x, (i + n))
type subst = subst_elt Prims.list
let (shift_subst_n :
  Prims.nat -> subst_elt Prims.list -> subst_elt Prims.list) =
  fun n -> FStar_List_Tot_Base.map (shift_subst_elt n)
let (shift_subst : subst_elt Prims.list -> subst_elt Prims.list) =
  shift_subst_n Prims.int_one
let (maybe_uniq_of_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.var FStar_Pervasives_Native.option)
  =
  fun x ->
    match FStar_Reflection_V2_Builtins.inspect_ln x with
    | FStar_Reflection_V2_Data.Tv_Var namedv ->
        FStar_Pervasives_Native.Some (namedv_uniq namedv)
    | uu___ -> FStar_Pervasives_Native.None
let rec (find_matching_subst_elt_bv :
  subst ->
    FStar_Reflection_Types.bv -> subst_elt FStar_Pervasives_Native.option)
  =
  fun s ->
    fun bv ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | (DT (j, t))::ss ->
          if j = (bv_index bv)
          then FStar_Pervasives_Native.Some (DT (j, t))
          else find_matching_subst_elt_bv ss bv
      | uu___::ss -> find_matching_subst_elt_bv ss bv
let (subst_db :
  FStar_Reflection_Types.bv -> subst -> FStar_Reflection_Types.term) =
  fun bv ->
    fun s ->
      match find_matching_subst_elt_bv s bv with
      | FStar_Pervasives_Native.Some (DT (uu___, t)) ->
          (match maybe_uniq_of_term t with
           | FStar_Pervasives_Native.None -> t
           | FStar_Pervasives_Native.Some k ->
               let v =
                 FStar_Reflection_V2_Builtins.pack_namedv
                   {
                     FStar_Reflection_V2_Data.uniq = k;
                     FStar_Reflection_V2_Data.sort =
                       ((FStar_Reflection_V2_Builtins.inspect_bv bv).FStar_Reflection_V2_Data.sort1);
                     FStar_Reflection_V2_Data.ppname =
                       ((FStar_Reflection_V2_Builtins.inspect_bv bv).FStar_Reflection_V2_Data.ppname1)
                   } in
               FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_Var v))
      | uu___ ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_BVar bv)
let rec (find_matching_subst_elt_var :
  subst ->
    FStar_Reflection_Types.namedv -> subst_elt FStar_Pervasives_Native.option)
  =
  fun s ->
    fun v ->
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
let (subst_var :
  FStar_Reflection_Types.namedv -> subst -> FStar_Reflection_Types.term) =
  fun v ->
    fun s ->
      match find_matching_subst_elt_var s v with
      | FStar_Pervasives_Native.Some (NT (uu___, t)) ->
          (match maybe_uniq_of_term t with
           | FStar_Pervasives_Native.None -> t
           | FStar_Pervasives_Native.Some k ->
               FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_Var
                    (FStar_Reflection_V2_Builtins.pack_namedv
                       (let uu___1 =
                          FStar_Reflection_V2_Builtins.inspect_namedv v in
                        {
                          FStar_Reflection_V2_Data.uniq = k;
                          FStar_Reflection_V2_Data.sort =
                            (uu___1.FStar_Reflection_V2_Data.sort);
                          FStar_Reflection_V2_Data.ppname =
                            (uu___1.FStar_Reflection_V2_Data.ppname)
                        }))))
      | FStar_Pervasives_Native.Some (ND (uu___, i)) ->
          let bv =
            FStar_Reflection_V2_Builtins.pack_bv
              {
                FStar_Reflection_V2_Data.index = i;
                FStar_Reflection_V2_Data.sort1 =
                  ((FStar_Reflection_V2_Builtins.inspect_namedv v).FStar_Reflection_V2_Data.sort);
                FStar_Reflection_V2_Data.ppname1 =
                  ((FStar_Reflection_V2_Builtins.inspect_namedv v).FStar_Reflection_V2_Data.ppname)
              } in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_BVar bv)
      | uu___ ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_Var v)
let (make_bv : Prims.nat -> FStar_Reflection_V2_Data.bv_view) =
  fun n ->
    {
      FStar_Reflection_V2_Data.index = n;
      FStar_Reflection_V2_Data.sort1 = sort_default;
      FStar_Reflection_V2_Data.ppname1 = pp_name_default
    }
let (make_bv_with_name :
  pp_name_t -> Prims.nat -> FStar_Reflection_V2_Data.bv_view) =
  fun s ->
    fun n ->
      {
        FStar_Reflection_V2_Data.index = n;
        FStar_Reflection_V2_Data.sort1 = sort_default;
        FStar_Reflection_V2_Data.ppname1 = s
      }
let (var_as_bv : Prims.nat -> FStar_Reflection_Types.bv) =
  fun v -> FStar_Reflection_V2_Builtins.pack_bv (make_bv v)
let (make_namedv : Prims.nat -> FStar_Reflection_V2_Data.namedv_view) =
  fun n ->
    {
      FStar_Reflection_V2_Data.uniq = n;
      FStar_Reflection_V2_Data.sort = sort_default;
      FStar_Reflection_V2_Data.ppname = pp_name_default
    }
let (make_namedv_with_name :
  pp_name_t -> Prims.nat -> FStar_Reflection_V2_Data.namedv_view) =
  fun s ->
    fun n ->
      {
        FStar_Reflection_V2_Data.uniq = n;
        FStar_Reflection_V2_Data.sort = sort_default;
        FStar_Reflection_V2_Data.ppname = s
      }
let (var_as_namedv : Prims.nat -> FStar_Reflection_Types.namedv) =
  fun v ->
    FStar_Reflection_V2_Builtins.pack_namedv
      {
        FStar_Reflection_V2_Data.uniq = v;
        FStar_Reflection_V2_Data.sort = sort_default;
        FStar_Reflection_V2_Data.ppname = pp_name_default
      }
let (var_as_term :
  FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term) =
  fun v ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Var (var_as_namedv v))
let (binder_of_t_q :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv -> FStar_Reflection_Types.binder)
  = fun t -> fun q -> mk_binder pp_name_default t q
let (mk_abs :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun t ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_Abs ((binder_of_t_q ty qual), t))
let (mk_total : FStar_Reflection_Types.typ -> FStar_Reflection_Types.comp) =
  fun t ->
    FStar_Reflection_V2_Builtins.pack_comp
      (FStar_Reflection_V2_Data.C_Total t)
let (mk_ghost : FStar_Reflection_Types.typ -> FStar_Reflection_Types.comp) =
  fun t ->
    FStar_Reflection_V2_Builtins.pack_comp
      (FStar_Reflection_V2_Data.C_GTotal t)
let (mk_arrow :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv ->
      FStar_Reflection_Types.typ -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun t ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_Arrow
             ((binder_of_t_q ty qual), (mk_total t)))
let (mk_ghost_arrow :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv ->
      FStar_Reflection_Types.typ -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun t ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_Arrow
             ((binder_of_t_q ty qual), (mk_ghost t)))
let (bound_var : Prims.nat -> FStar_Reflection_Types.term) =
  fun i ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_BVar
         (FStar_Reflection_V2_Builtins.pack_bv (make_bv i)))
let (mk_let :
  pp_name_t ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ppname ->
    fun e1 ->
      fun t1 ->
        fun e2 ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_Let
               (false, [], (mk_simple_binder ppname t1), e1, e2))
let (open_with_var_elt :
  FStar_Reflection_V2_Data.var -> Prims.nat -> subst_elt) =
  fun x ->
    fun i ->
      DT
        (i,
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_Var (var_as_namedv x))))
let (open_with_var : FStar_Reflection_V2_Data.var -> Prims.nat -> subst) =
  fun x -> fun i -> [open_with_var_elt x i]
let (subst_ctx_uvar_and_subst :
  FStar_Reflection_Types.ctx_uvar_and_subst ->
    subst -> FStar_Reflection_Types.ctx_uvar_and_subst)
  = fun uu___ -> fun uu___1 -> Prims.magic ()
let rec (binder_offset_patterns :
  (FStar_Reflection_V2_Data.pattern * Prims.bool) Prims.list -> Prims.nat) =
  fun ps ->
    match ps with
    | [] -> Prims.int_zero
    | (p, b)::ps1 ->
        let n = binder_offset_pattern p in
        let m = binder_offset_patterns ps1 in n + m
and (binder_offset_pattern : FStar_Reflection_V2_Data.pattern -> Prims.nat) =
  fun p ->
    match p with
    | FStar_Reflection_V2_Data.Pat_Constant uu___ -> Prims.int_zero
    | FStar_Reflection_V2_Data.Pat_Dot_Term uu___ -> Prims.int_zero
    | FStar_Reflection_V2_Data.Pat_Var (uu___, uu___1) -> Prims.int_one
    | FStar_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
        binder_offset_patterns subpats
let (open_with :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.open_with t v
let (open_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.open_term t v
let (close_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.close_term t v
let (rename :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.var ->
      FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  = fun t -> fun x -> fun y -> FStar_Reflection_Typing_Builtins.rename t x y
let (constant_as_term :
  FStar_Reflection_V2_Data.vconst -> FStar_Reflection_Types.term) =
  fun v ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Const v)
let (unit_exp : FStar_Reflection_Types.term) =
  constant_as_term FStar_Reflection_V2_Data.C_Unit
let (unit_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.unit_lid
let (unit_ty : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar unit_fv)
let (bool_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.bool_lid
let (bool_ty : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar bool_fv)
let (u_zero : FStar_Reflection_Types.universe) =
  FStar_Reflection_V2_Builtins.pack_universe FStar_Reflection_V2_Data.Uv_Zero
let (u_max :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe -> FStar_Reflection_Types.universe)
  =
  fun u1 ->
    fun u2 ->
      FStar_Reflection_V2_Builtins.pack_universe
        (FStar_Reflection_V2_Data.Uv_Max [u1; u2])
let (u_succ :
  FStar_Reflection_Types.universe -> FStar_Reflection_Types.universe) =
  fun u ->
    FStar_Reflection_V2_Builtins.pack_universe
      (FStar_Reflection_V2_Data.Uv_Succ u)
let (tm_type :
  FStar_Reflection_Types.universe -> FStar_Reflection_Types.term) =
  fun u ->
    FStar_Reflection_V2_Builtins.pack_ln (FStar_Reflection_V2_Data.Tv_Type u)
let (tm_prop : FStar_Reflection_Types.term) =
  let prop_fv =
    FStar_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.prop_qn in
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar prop_fv)
let (eqtype_lid : FStar_Reflection_Types.name) = ["Prims"; "eqtype"]
let (true_bool : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_True)
let (false_bool : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_False)
let (eq2 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun v0 ->
        fun v1 ->
          let eq21 =
            FStar_Reflection_V2_Builtins.pack_fv
              FStar_Reflection_Const.eq2_qn in
          let eq22 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst (eq21, [u])) in
          let h =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (eq22, (t, FStar_Reflection_V2_Data.Q_Implicit))) in
          let h1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (h, (v0, FStar_Reflection_V2_Data.Q_Explicit))) in
          let h2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (h1, (v1, FStar_Reflection_V2_Data.Q_Explicit))) in
          h2
let (b2t_lid : FStar_Reflection_Types.name) = ["Prims"; "b2t"]
let (b2t_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv b2t_lid
let (b2t_ty : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_Arrow
       ((mk_binder (FStar_Sealed.seal "x") bool_ty
           FStar_Reflection_V2_Data.Q_Explicit), (mk_total (tm_type u_zero))))
type term_ctxt =
  | Ctxt_hole 
  | Ctxt_app_head of term_ctxt * FStar_Reflection_V2_Data.argv 
  | Ctxt_app_arg of FStar_Reflection_Types.term *
  FStar_Reflection_V2_Data.aqualv * term_ctxt 
let uu___is_Ctxt_hole uu___ =
  match uu___ with | Ctxt_hole _ -> true | _ -> false
let uu___is_Ctxt_app_head uu___ =
  match uu___ with | Ctxt_app_head _ -> true | _ -> false
let uu___is_Ctxt_app_arg uu___ =
  match uu___ with | Ctxt_app_arg _ -> true | _ -> false
let rec (apply_term_ctxt :
  term_ctxt -> FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun e ->
    fun t ->
      match e with
      | Ctxt_hole -> t
      | Ctxt_app_head (e1, arg) ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App ((apply_term_ctxt e1 t), arg))
      | Ctxt_app_arg (hd, q, e1) ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (hd, ((apply_term_ctxt e1 t), q)))
let (mk_if :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun scrutinee ->
    fun then_ ->
      fun else_ ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_Match
             (scrutinee, FStar_Pervasives_Native.None,
               [((FStar_Reflection_V2_Data.Pat_Constant
                    FStar_Reflection_V2_Data.C_True), then_);
               ((FStar_Reflection_V2_Data.Pat_Constant
                   FStar_Reflection_V2_Data.C_False), else_)]))
type comp_typ =
  (FStar_TypeChecker_Core.tot_or_ghost * FStar_Reflection_Types.typ)
let (mk_comp : comp_typ -> FStar_Reflection_Types.comp) =
  fun c ->
    match FStar_Pervasives_Native.fst c with
    | FStar_TypeChecker_Core.E_Total ->
        mk_total (FStar_Pervasives_Native.snd c)
    | FStar_TypeChecker_Core.E_Ghost ->
        mk_ghost (FStar_Pervasives_Native.snd c)
let (mk_arrow_ct :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv ->
      comp_typ -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun c ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_Arrow
             ((binder_of_t_q ty qual), (mk_comp c)))
type relation =
  | R_Eq 
  | R_Sub 
let (uu___is_R_Eq : relation -> Prims.bool) =
  fun projectee -> match projectee with | R_Eq -> true | uu___ -> false
let (uu___is_R_Sub : relation -> Prims.bool) =
  fun projectee -> match projectee with | R_Sub -> true | uu___ -> false
type binding = (FStar_Reflection_V2_Data.var * FStar_Reflection_Types.term)
type bindings = binding Prims.list
let rename_bindings :
  'uuuuu .
    ('uuuuu * FStar_Reflection_Types.term) Prims.list ->
      FStar_Reflection_V2_Data.var ->
        FStar_Reflection_V2_Data.var ->
          ('uuuuu * FStar_Reflection_Types.term) Prims.list
  =
  fun bs ->
    fun x ->
      fun y ->
        FStar_List_Tot_Base.map
          (fun uu___ -> match uu___ with | (v, t) -> (v, (rename t x y))) bs
let rec (extend_env_l :
  FStar_Reflection_Types.env -> bindings -> FStar_Reflection_Types.env) =
  fun g ->
    fun bs ->
      match bs with
      | [] -> g
      | (x, t)::bs1 -> extend_env (extend_env_l g bs1) x t
let (is_non_informative_name : FStar_Reflection_Types.name -> Prims.bool) =
  fun l ->
    ((l = FStar_Reflection_Const.unit_lid) ||
       (l = FStar_Reflection_Const.squash_qn))
      || (l = ["FStar"; "Ghost"; "erased"])
let (is_non_informative_fv : FStar_Reflection_Types.fv -> Prims.bool) =
  fun f ->
    is_non_informative_name (FStar_Reflection_V2_Builtins.inspect_fv f)
let (bindings_to_refl_bindings :
  binding Prims.list -> FStar_Reflection_V2_Data.binding Prims.list) =
  fun bs ->
    FStar_List_Tot_Base.map
      (fun uu___ ->
         match uu___ with
         | (v, ty) ->
             {
               FStar_Reflection_V2_Data.uniq1 = v;
               FStar_Reflection_V2_Data.sort3 = ty;
               FStar_Reflection_V2_Data.ppname3 = pp_name_default
             }) bs
let (refl_bindings_to_bindings :
  FStar_Reflection_V2_Data.binding Prims.list -> binding Prims.list) =
  fun bs ->
    FStar_List_Tot_Base.map
      (fun b ->
         ((b.FStar_Reflection_V2_Data.uniq1),
           (b.FStar_Reflection_V2_Data.sort3))) bs
type ('env, 'bnds, 'pat) bindings_ok_for_pat = unit
type ('g, 'bs, 'br) bindings_ok_for_branch = unit
type ('g, 'bss, 'brs) bindings_ok_for_branch_N = Obj.t
let (binding_to_namedv :
  FStar_Reflection_V2_Data.binding -> FStar_Reflection_Types.namedv) =
  fun b ->
    FStar_Reflection_V2_Builtins.pack_namedv
      {
        FStar_Reflection_V2_Data.uniq = (b.FStar_Reflection_V2_Data.uniq1);
        FStar_Reflection_V2_Data.sort =
          (FStar_Sealed.seal b.FStar_Reflection_V2_Data.sort3);
        FStar_Reflection_V2_Data.ppname =
          (b.FStar_Reflection_V2_Data.ppname3)
      }
let rec (elaborate_pat :
  FStar_Reflection_V2_Data.pattern ->
    FStar_Reflection_V2_Data.binding Prims.list ->
      (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.binding
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun p ->
    fun bs ->
      match (p, bs) with
      | (FStar_Reflection_V2_Data.Pat_Constant c, uu___) ->
          FStar_Pervasives_Native.Some
            ((FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_Const c)), bs)
      | (FStar_Reflection_V2_Data.Pat_Cons (fv, univs, subpats), bs1) ->
          let head =
            match univs with
            | FStar_Pervasives_Native.Some univs1 ->
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_UInst (fv, univs1))
            | FStar_Pervasives_Native.None ->
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_FVar fv) in
          fold_left_dec (FStar_Pervasives_Native.Some (head, bs1)) subpats
            (fun st ->
               fun pi ->
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
                                 ((FStar_Reflection_V2_Builtins.pack_ln
                                     (FStar_Reflection_V2_Data.Tv_App
                                        (head1,
                                          (t,
                                            (if i
                                             then
                                               FStar_Reflection_V2_Data.Q_Implicit
                                             else
                                               FStar_Reflection_V2_Data.Q_Explicit))))),
                                   bs'))))
      | (FStar_Reflection_V2_Data.Pat_Var (uu___, uu___1), b::bs1) ->
          FStar_Pervasives_Native.Some
            ((FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_Var (binding_to_namedv b))),
              bs1)
      | (FStar_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.Some
         t), uu___) -> FStar_Pervasives_Native.Some (t, bs)
      | (FStar_Reflection_V2_Data.Pat_Dot_Term
         (FStar_Pervasives_Native.None), uu___) ->
          FStar_Pervasives_Native.None
      | uu___ -> FStar_Pervasives_Native.None
type ('g, 't1, 't2) sub_typing = unit
type ('g, 'c1, 'c2) sub_comp = unit
type ('g, 't1, 't2) equiv = unit
type ('g, 'e, 't) tot_typing = unit
type ('g, 'e, 't) ghost_typing = unit
type 'g fstar_env_fvs = unit
type fstar_env = FStar_Reflection_Types.env
type fstar_top_env = fstar_env
type blob = (Prims.string * FStar_Reflection_Types.term)
type ('s, 't) sigelt_has_type = Obj.t
type ('g, 't) sigelt_for =
  (Prims.bool * FStar_Reflection_Types.sigelt * blob
    FStar_Pervasives_Native.option)
type ('g, 't) dsl_tac_result_t =
  ((unit, unit) sigelt_for Prims.list * (unit, unit) sigelt_for * (unit,
    unit) sigelt_for Prims.list)
type dsl_tac_t =
  (fstar_top_env * FStar_Reflection_Types.typ FStar_Pervasives_Native.option)
    -> ((unit, unit) dsl_tac_result_t, unit) FStar_Tactics_Effect.tac_repr
let (if_complete_match :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (unit, unit, unit, unit, unit)
        FStar_Tactics_V2_Builtins.match_complete_token)
  = fun g -> fun t -> Prims.magic ()
let (mk_checked_let :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.name ->
      Prims.string ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.typ -> (unit, unit) sigelt_for)
  =
  fun g ->
    fun cur_module ->
      fun nm ->
        fun tm ->
          fun ty ->
            let fv =
              FStar_Reflection_V2_Builtins.pack_fv
                (FStar_List_Tot_Base.op_At cur_module [nm]) in
            let lb =
              FStar_Reflection_V2_Builtins.pack_lb
                {
                  FStar_Reflection_V2_Data.lb_fv = fv;
                  FStar_Reflection_V2_Data.lb_us = [];
                  FStar_Reflection_V2_Data.lb_typ = ty;
                  FStar_Reflection_V2_Data.lb_def = tm
                } in
            let se =
              FStar_Reflection_V2_Builtins.pack_sigelt
                (FStar_Reflection_V2_Data.Sg_Let (false, [lb])) in
            (true, se, FStar_Pervasives_Native.None)
let (mk_unchecked_let :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.name ->
      Prims.string ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.typ ->
            (Prims.bool * FStar_Reflection_Types.sigelt * blob
              FStar_Pervasives_Native.option))
  =
  fun g ->
    fun cur_module ->
      fun nm ->
        fun tm ->
          fun ty ->
            let fv =
              FStar_Reflection_V2_Builtins.pack_fv
                (FStar_List_Tot_Base.op_At cur_module [nm]) in
            let lb =
              FStar_Reflection_V2_Builtins.pack_lb
                {
                  FStar_Reflection_V2_Data.lb_fv = fv;
                  FStar_Reflection_V2_Data.lb_us = [];
                  FStar_Reflection_V2_Data.lb_typ = ty;
                  FStar_Reflection_V2_Data.lb_def = tm
                } in
            let se =
              FStar_Reflection_V2_Builtins.pack_sigelt
                (FStar_Reflection_V2_Data.Sg_Let (false, [lb])) in
            (false, se, FStar_Pervasives_Native.None)