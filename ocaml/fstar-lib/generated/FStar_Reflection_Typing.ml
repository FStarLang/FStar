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
  FStarC_Reflection_Types.env ->
    Prims.int -> FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun e -> fun x -> Prims.magic ()
let (lookup_fvar_uinst :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.fv ->
      FStarC_Reflection_Types.universe Prims.list ->
        FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun e -> fun x -> fun us -> Prims.magic ()
let (lookup_fvar :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.fv ->
      FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun e -> fun x -> lookup_fvar_uinst e x []
type pp_name_t = (Prims.string, unit) FStar_Sealed_Inhabited.sealed
let (pp_name_default : pp_name_t) = FStar_Sealed_Inhabited.seal "x" "x"
let (seal_pp_name : Prims.string -> pp_name_t) =
  fun x -> FStar_Sealed_Inhabited.seal "x" x
let (tun : FStarC_Reflection_Types.term) =
  FStarC_Reflection_V2_Builtins.pack_ln FStarC_Reflection_V2_Data.Tv_Unknown
type sort_t =
  (FStarC_Reflection_Types.term, unit) FStar_Sealed_Inhabited.sealed
let (sort_default : sort_t) = FStar_Sealed_Inhabited.seal tun tun
let (seal_sort : FStarC_Reflection_Types.term -> sort_t) =
  fun x -> FStar_Sealed_Inhabited.seal tun x
let (mk_binder :
  pp_name_t ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_V2_Data.aqualv -> FStarC_Reflection_Types.binder)
  =
  fun pp_name ->
    fun ty ->
      fun q ->
        FStarC_Reflection_V2_Builtins.pack_binder
          {
            FStarC_Reflection_V2_Data.sort2 = ty;
            FStarC_Reflection_V2_Data.qual = q;
            FStarC_Reflection_V2_Data.attrs = [];
            FStarC_Reflection_V2_Data.ppname2 = pp_name
          }
let (mk_simple_binder :
  pp_name_t ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_V2_Data.simple_binder)
  =
  fun pp_name ->
    fun ty ->
      FStarC_Reflection_V2_Builtins.pack_binder
        {
          FStarC_Reflection_V2_Data.sort2 = ty;
          FStarC_Reflection_V2_Data.qual =
            FStarC_Reflection_V2_Data.Q_Explicit;
          FStarC_Reflection_V2_Data.attrs = [];
          FStarC_Reflection_V2_Data.ppname2 = pp_name
        }
let (extend_env :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_V2_Data.var ->
      FStarC_Reflection_Types.term -> FStarC_Reflection_Types.env)
  =
  fun e ->
    fun x ->
      fun ty ->
        FStar_Reflection_V2_Derived.push_binding e
          {
            FStarC_Reflection_V2_Data.uniq1 = x;
            FStarC_Reflection_V2_Data.sort3 = ty;
            FStarC_Reflection_V2_Data.ppname3 = (seal_pp_name "x")
          }
let (bv_index : FStarC_Reflection_Types.bv -> FStarC_Reflection_V2_Data.var)
  =
  fun x ->
    (FStarC_Reflection_V2_Builtins.inspect_bv x).FStarC_Reflection_V2_Data.index
let (namedv_uniq :
  FStarC_Reflection_Types.namedv -> FStarC_Reflection_V2_Data.var) =
  fun x ->
    (FStarC_Reflection_V2_Builtins.inspect_namedv x).FStarC_Reflection_V2_Data.uniq
let (binder_sort :
  FStarC_Reflection_Types.binder -> FStarC_Reflection_Types.typ) =
  fun b ->
    (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2
let (binder_qual :
  FStarC_Reflection_Types.binder -> FStarC_Reflection_V2_Data.aqualv) =
  fun b ->
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
let (uu___is_DT : subst_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | DT (_0, _1) -> true | uu___ -> false
let (__proj__DT__item___0 : subst_elt -> Prims.nat) =
  fun projectee -> match projectee with | DT (_0, _1) -> _0
let (__proj__DT__item___1 : subst_elt -> FStarC_Reflection_Types.term) =
  fun projectee -> match projectee with | DT (_0, _1) -> _1
let (uu___is_NT : subst_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | NT (_0, _1) -> true | uu___ -> false
let (__proj__NT__item___0 : subst_elt -> FStarC_Reflection_V2_Data.var) =
  fun projectee -> match projectee with | NT (_0, _1) -> _0
let (__proj__NT__item___1 : subst_elt -> FStarC_Reflection_Types.term) =
  fun projectee -> match projectee with | NT (_0, _1) -> _1
let (uu___is_ND : subst_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | ND (_0, _1) -> true | uu___ -> false
let (__proj__ND__item___0 : subst_elt -> FStarC_Reflection_V2_Data.var) =
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
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.var FStar_Pervasives_Native.option)
  =
  fun x ->
    match FStarC_Reflection_V2_Builtins.inspect_ln x with
    | FStarC_Reflection_V2_Data.Tv_Var namedv ->
        FStar_Pervasives_Native.Some (namedv_uniq namedv)
    | uu___ -> FStar_Pervasives_Native.None
let rec (find_matching_subst_elt_bv :
  subst ->
    FStarC_Reflection_Types.bv -> subst_elt FStar_Pervasives_Native.option)
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
  FStarC_Reflection_Types.bv -> subst -> FStarC_Reflection_Types.term) =
  fun bv ->
    fun s ->
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
let rec (find_matching_subst_elt_var :
  subst ->
    FStarC_Reflection_Types.namedv ->
      subst_elt FStar_Pervasives_Native.option)
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
  FStarC_Reflection_Types.namedv -> subst -> FStarC_Reflection_Types.term) =
  fun v ->
    fun s ->
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
let (make_bv : Prims.nat -> FStarC_Reflection_V2_Data.bv_view) =
  fun n ->
    {
      FStarC_Reflection_V2_Data.index = n;
      FStarC_Reflection_V2_Data.sort1 = sort_default;
      FStarC_Reflection_V2_Data.ppname1 = pp_name_default
    }
let (make_bv_with_name :
  pp_name_t -> Prims.nat -> FStarC_Reflection_V2_Data.bv_view) =
  fun s ->
    fun n ->
      {
        FStarC_Reflection_V2_Data.index = n;
        FStarC_Reflection_V2_Data.sort1 = sort_default;
        FStarC_Reflection_V2_Data.ppname1 = s
      }
let (var_as_bv : Prims.nat -> FStarC_Reflection_Types.bv) =
  fun v -> FStarC_Reflection_V2_Builtins.pack_bv (make_bv v)
let (make_namedv : Prims.nat -> FStarC_Reflection_V2_Data.namedv_view) =
  fun n ->
    {
      FStarC_Reflection_V2_Data.uniq = n;
      FStarC_Reflection_V2_Data.sort = sort_default;
      FStarC_Reflection_V2_Data.ppname = pp_name_default
    }
let (make_namedv_with_name :
  pp_name_t -> Prims.nat -> FStarC_Reflection_V2_Data.namedv_view) =
  fun s ->
    fun n ->
      {
        FStarC_Reflection_V2_Data.uniq = n;
        FStarC_Reflection_V2_Data.sort = sort_default;
        FStarC_Reflection_V2_Data.ppname = s
      }
let (var_as_namedv : Prims.nat -> FStarC_Reflection_Types.namedv) =
  fun v ->
    FStarC_Reflection_V2_Builtins.pack_namedv
      {
        FStarC_Reflection_V2_Data.uniq = v;
        FStarC_Reflection_V2_Data.sort = sort_default;
        FStarC_Reflection_V2_Data.ppname = pp_name_default
      }
let (var_as_term :
  FStarC_Reflection_V2_Data.var -> FStarC_Reflection_Types.term) =
  fun v ->
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_Var (var_as_namedv v))
let (binder_of_t_q :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.aqualv -> FStarC_Reflection_Types.binder)
  = fun t -> fun q -> mk_binder pp_name_default t q
let (mk_abs :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.aqualv ->
      FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun t ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_Abs ((binder_of_t_q ty qual), t))
let (mk_total : FStarC_Reflection_Types.typ -> FStarC_Reflection_Types.comp)
  =
  fun t ->
    FStarC_Reflection_V2_Builtins.pack_comp
      (FStarC_Reflection_V2_Data.C_Total t)
let (mk_ghost : FStarC_Reflection_Types.typ -> FStarC_Reflection_Types.comp)
  =
  fun t ->
    FStarC_Reflection_V2_Builtins.pack_comp
      (FStarC_Reflection_V2_Data.C_GTotal t)
let (mk_arrow :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.aqualv ->
      FStarC_Reflection_Types.typ -> FStarC_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun t ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_Arrow
             ((binder_of_t_q ty qual), (mk_total t)))
let (mk_ghost_arrow :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.aqualv ->
      FStarC_Reflection_Types.typ -> FStarC_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun t ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_Arrow
             ((binder_of_t_q ty qual), (mk_ghost t)))
let (bound_var : Prims.nat -> FStarC_Reflection_Types.term) =
  fun i ->
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_BVar
         (FStarC_Reflection_V2_Builtins.pack_bv (make_bv i)))
let (mk_let :
  pp_name_t ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun ppname ->
    fun e1 ->
      fun t1 ->
        fun e2 ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Let
               (false, [], (mk_simple_binder ppname t1), e1, e2))
let (open_with_var_elt :
  FStarC_Reflection_V2_Data.var -> Prims.nat -> subst_elt) =
  fun x ->
    fun i ->
      DT
        (i,
          (FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_Var (var_as_namedv x))))
let (open_with_var : FStarC_Reflection_V2_Data.var -> Prims.nat -> subst) =
  fun x -> fun i -> [open_with_var_elt x i]
let (subst_ctx_uvar_and_subst :
  FStarC_Reflection_Types.ctx_uvar_and_subst ->
    subst -> FStarC_Reflection_Types.ctx_uvar_and_subst)
  = fun uu___ -> fun uu___1 -> Prims.magic ()
let rec (binder_offset_patterns :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) Prims.list -> Prims.nat) =
  fun ps ->
    match ps with
    | [] -> Prims.int_zero
    | (p, b)::ps1 ->
        let n = binder_offset_pattern p in
        let m = binder_offset_patterns ps1 in n + m
and (binder_offset_pattern : FStarC_Reflection_V2_Data.pattern -> Prims.nat)
  =
  fun p ->
    match p with
    | FStarC_Reflection_V2_Data.Pat_Constant uu___ -> Prims.int_zero
    | FStarC_Reflection_V2_Data.Pat_Dot_Term uu___ -> Prims.int_zero
    | FStarC_Reflection_V2_Data.Pat_Var (uu___, uu___1) -> Prims.int_one
    | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
        binder_offset_patterns subpats
let rec (subst_term :
  FStarC_Reflection_Types.term -> subst -> FStarC_Reflection_Types.term) =
  fun t ->
    fun ss ->
      match FStarC_Reflection_V2_Builtins.inspect_ln t with
      | FStarC_Reflection_V2_Data.Tv_UInst (uu___, uu___1) -> t
      | FStarC_Reflection_V2_Data.Tv_FVar uu___ -> t
      | FStarC_Reflection_V2_Data.Tv_Type uu___ -> t
      | FStarC_Reflection_V2_Data.Tv_Const uu___ -> t
      | FStarC_Reflection_V2_Data.Tv_Unsupp -> t
      | FStarC_Reflection_V2_Data.Tv_Unknown -> t
      | FStarC_Reflection_V2_Data.Tv_Var x -> subst_var x ss
      | FStarC_Reflection_V2_Data.Tv_BVar j -> subst_db j ss
      | FStarC_Reflection_V2_Data.Tv_App (hd, argv) ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               ((subst_term hd ss),
                 ((subst_term (FStar_Pervasives_Native.fst argv) ss),
                   (FStar_Pervasives_Native.snd argv))))
      | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
          let b' = subst_binder b ss in
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Abs
               (b', (subst_term body (shift_subst ss))))
      | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
          let b' = subst_binder b ss in
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Arrow
               (b', (subst_comp c (shift_subst ss))))
      | FStarC_Reflection_V2_Data.Tv_Refine (b, f) ->
          let b1 = subst_binder b ss in
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Refine
               (b1, (subst_term f (shift_subst ss))))
      | FStarC_Reflection_V2_Data.Tv_Uvar (j, c) ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Uvar
               (j, (subst_ctx_uvar_and_subst c ss)))
      | FStarC_Reflection_V2_Data.Tv_Let (recf, attrs, b, def, body) ->
          let b1 = subst_binder b ss in
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Let
               (recf, (subst_terms attrs ss), b1,
                 (if recf
                  then subst_term def (shift_subst ss)
                  else subst_term def ss),
                 (subst_term body (shift_subst ss))))
      | FStarC_Reflection_V2_Data.Tv_Match (scr, ret, brs) ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Match
               ((subst_term scr ss),
                 (match ret with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some m ->
                      FStar_Pervasives_Native.Some (subst_match_returns m ss)),
                 (subst_branches brs ss)))
      | FStarC_Reflection_V2_Data.Tv_AscribedT (e, t1, tac, b) ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_AscribedT
               ((subst_term e ss), (subst_term t1 ss),
                 (match tac with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some tac1 ->
                      FStar_Pervasives_Native.Some (subst_term tac1 ss)), b))
      | FStarC_Reflection_V2_Data.Tv_AscribedC (e, c, tac, b) ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_AscribedC
               ((subst_term e ss), (subst_comp c ss),
                 (match tac with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some tac1 ->
                      FStar_Pervasives_Native.Some (subst_term tac1 ss)), b))
and (subst_binder :
  FStarC_Reflection_Types.binder -> subst -> FStarC_Reflection_Types.binder)
  =
  fun b ->
    fun ss ->
      let bndr = FStarC_Reflection_V2_Builtins.inspect_binder b in
      FStarC_Reflection_V2_Builtins.pack_binder
        {
          FStarC_Reflection_V2_Data.sort2 =
            (subst_term bndr.FStarC_Reflection_V2_Data.sort2 ss);
          FStarC_Reflection_V2_Data.qual =
            (bndr.FStarC_Reflection_V2_Data.qual);
          FStarC_Reflection_V2_Data.attrs =
            (subst_terms bndr.FStarC_Reflection_V2_Data.attrs ss);
          FStarC_Reflection_V2_Data.ppname2 =
            (bndr.FStarC_Reflection_V2_Data.ppname2)
        }
and (subst_comp :
  FStarC_Reflection_Types.comp -> subst -> FStarC_Reflection_Types.comp) =
  fun c ->
    fun ss ->
      match FStarC_Reflection_V2_Builtins.inspect_comp c with
      | FStarC_Reflection_V2_Data.C_Total t ->
          FStarC_Reflection_V2_Builtins.pack_comp
            (FStarC_Reflection_V2_Data.C_Total (subst_term t ss))
      | FStarC_Reflection_V2_Data.C_GTotal t ->
          FStarC_Reflection_V2_Builtins.pack_comp
            (FStarC_Reflection_V2_Data.C_GTotal (subst_term t ss))
      | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
          FStarC_Reflection_V2_Builtins.pack_comp
            (FStarC_Reflection_V2_Data.C_Lemma
               ((subst_term pre ss), (subst_term post ss),
                 (subst_term pats ss)))
      | FStarC_Reflection_V2_Data.C_Eff (us, eff_name, res, args, decrs) ->
          FStarC_Reflection_V2_Builtins.pack_comp
            (FStarC_Reflection_V2_Data.C_Eff
               (us, eff_name, (subst_term res ss), (subst_args args ss),
                 (subst_terms decrs ss)))
and (subst_terms :
  FStarC_Reflection_Types.term Prims.list ->
    subst -> FStarC_Reflection_Types.term Prims.list)
  =
  fun ts ->
    fun ss ->
      match ts with
      | [] -> []
      | t::ts1 -> (subst_term t ss) :: (subst_terms ts1 ss)
and (subst_args :
  FStarC_Reflection_V2_Data.argv Prims.list ->
    subst -> FStarC_Reflection_V2_Data.argv Prims.list)
  =
  fun ts ->
    fun ss ->
      match ts with
      | [] -> []
      | (t, q)::ts1 -> ((subst_term t ss), q) :: (subst_args ts1 ss)
and (subst_patterns :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) Prims.list ->
    subst -> (FStarC_Reflection_V2_Data.pattern * Prims.bool) Prims.list)
  =
  fun ps ->
    fun ss ->
      match ps with
      | [] -> ps
      | (p, b)::ps1 ->
          let n = binder_offset_pattern p in
          let p1 = subst_pattern p ss in
          let ps2 = subst_patterns ps1 (shift_subst_n n ss) in (p1, b) :: ps2
and (subst_pattern :
  FStarC_Reflection_V2_Data.pattern ->
    subst -> FStarC_Reflection_V2_Data.pattern)
  =
  fun p ->
    fun ss ->
      match p with
      | FStarC_Reflection_V2_Data.Pat_Constant uu___ -> p
      | FStarC_Reflection_V2_Data.Pat_Cons (fv, us, pats) ->
          let pats1 = subst_patterns pats ss in
          FStarC_Reflection_V2_Data.Pat_Cons (fv, us, pats1)
      | FStarC_Reflection_V2_Data.Pat_Var (bv, s) ->
          FStarC_Reflection_V2_Data.Pat_Var (bv, s)
      | FStarC_Reflection_V2_Data.Pat_Dot_Term topt ->
          FStarC_Reflection_V2_Data.Pat_Dot_Term
            ((match topt with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some t ->
                  FStar_Pervasives_Native.Some (subst_term t ss)))
and (subst_branch :
  FStarC_Reflection_V2_Data.branch ->
    subst -> FStarC_Reflection_V2_Data.branch)
  =
  fun br ->
    fun ss ->
      let uu___ = br in
      match uu___ with
      | (p, t) ->
          let p1 = subst_pattern p ss in
          let j = binder_offset_pattern p1 in
          let t1 = subst_term t (shift_subst_n j ss) in (p1, t1)
and (subst_branches :
  FStarC_Reflection_V2_Data.branch Prims.list ->
    subst -> FStarC_Reflection_V2_Data.branch Prims.list)
  =
  fun brs ->
    fun ss ->
      match brs with
      | [] -> []
      | br::brs1 -> (subst_branch br ss) :: (subst_branches brs1 ss)
and (subst_match_returns :
  FStarC_Syntax_Syntax.match_returns_ascription ->
    subst -> FStarC_Syntax_Syntax.match_returns_ascription)
  =
  fun m ->
    fun ss ->
      let uu___ = m in
      match uu___ with
      | (b, (ret, as_, eq)) ->
          let b1 = subst_binder b ss in
          let ret1 =
            match ret with
            | FStar_Pervasives.Inl t ->
                FStar_Pervasives.Inl (subst_term t (shift_subst ss))
            | FStar_Pervasives.Inr c ->
                FStar_Pervasives.Inr (subst_comp c (shift_subst ss)) in
          let as_1 =
            match as_ with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some t ->
                FStar_Pervasives_Native.Some (subst_term t (shift_subst ss)) in
          (b1, (ret1, as_1, eq))
let (open_with :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.open_with t v
let (open_term :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.var -> FStarC_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.open_term t v
let (close_term :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.var -> FStarC_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.close_term t v
let (rename :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.var ->
      FStarC_Reflection_V2_Data.var -> FStarC_Reflection_Types.term)
  = fun t -> fun x -> fun y -> FStar_Reflection_Typing_Builtins.rename t x y
let (constant_as_term :
  FStarC_Reflection_V2_Data.vconst -> FStarC_Reflection_Types.term) =
  fun v ->
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_Const v)
let (unit_exp : FStarC_Reflection_Types.term) =
  constant_as_term FStarC_Reflection_V2_Data.C_Unit
let (unit_fv : FStarC_Reflection_Types.fv) =
  FStarC_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.unit_lid
let (unit_ty : FStarC_Reflection_Types.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar unit_fv)
let (bool_fv : FStarC_Reflection_Types.fv) =
  FStarC_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.bool_lid
let (bool_ty : FStarC_Reflection_Types.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar bool_fv)
let (u_zero : FStarC_Reflection_Types.universe) =
  FStarC_Reflection_V2_Builtins.pack_universe
    FStarC_Reflection_V2_Data.Uv_Zero
let (u_max :
  FStarC_Reflection_Types.universe ->
    FStarC_Reflection_Types.universe -> FStarC_Reflection_Types.universe)
  =
  fun u1 ->
    fun u2 ->
      FStarC_Reflection_V2_Builtins.pack_universe
        (FStarC_Reflection_V2_Data.Uv_Max [u1; u2])
let (u_succ :
  FStarC_Reflection_Types.universe -> FStarC_Reflection_Types.universe) =
  fun u ->
    FStarC_Reflection_V2_Builtins.pack_universe
      (FStarC_Reflection_V2_Data.Uv_Succ u)
let (tm_type :
  FStarC_Reflection_Types.universe -> FStarC_Reflection_Types.term) =
  fun u ->
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_Type u)
let (tm_prop : FStarC_Reflection_Types.term) =
  let prop_fv =
    FStarC_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.prop_qn in
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar prop_fv)
let (eqtype_lid : FStarC_Reflection_Types.name) = ["Prims"; "eqtype"]
let (true_bool : FStarC_Reflection_Types.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_True)
let (false_bool : FStarC_Reflection_Types.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_False)
let (eq2 :
  FStarC_Reflection_Types.universe ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun v0 ->
        fun v1 ->
          let eq21 =
            FStarC_Reflection_V2_Builtins.pack_fv
              FStar_Reflection_Const.eq2_qn in
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
let (b2t_lid : FStarC_Reflection_Types.name) = ["Prims"; "b2t"]
let (b2t_fv : FStarC_Reflection_Types.fv) =
  FStarC_Reflection_V2_Builtins.pack_fv b2t_lid
let (b2t_ty : FStarC_Reflection_Types.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Arrow
       ((mk_binder (FStar_Sealed.seal "x") bool_ty
           FStarC_Reflection_V2_Data.Q_Explicit),
         (mk_total (tm_type u_zero))))
let rec (freevars :
  FStarC_Reflection_Types.term -> FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun e ->
    match FStarC_Reflection_V2_Builtins.inspect_ln e with
    | FStarC_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) ->
        FStar_Set.complement (FStar_Set.empty ())
    | FStarC_Reflection_V2_Data.Tv_UInst (uu___, uu___1) ->
        FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Tv_FVar uu___ -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Tv_Type uu___ -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Tv_Const uu___ -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Tv_Unknown -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Tv_Unsupp -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Tv_BVar uu___ -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Tv_Var x ->
        FStar_Set.singleton (namedv_uniq x)
    | FStarC_Reflection_V2_Data.Tv_App (e1, (e2, uu___)) ->
        FStar_Set.union (freevars e1) (freevars e2)
    | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
        FStar_Set.union (freevars_binder b) (freevars body)
    | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
        FStar_Set.union (freevars_binder b) (freevars_comp c)
    | FStarC_Reflection_V2_Data.Tv_Refine (b, f) ->
        FStar_Set.union (freevars (binder_sort b)) (freevars f)
    | FStarC_Reflection_V2_Data.Tv_Let (recf, attrs, b, def, body) ->
        FStar_Set.union
          (FStar_Set.union
             (FStar_Set.union (freevars_terms attrs)
                (freevars (binder_sort b))) (freevars def)) (freevars body)
    | FStarC_Reflection_V2_Data.Tv_Match (scr, ret, brs) ->
        FStar_Set.union
          (FStar_Set.union (freevars scr)
             (freevars_opt ret freevars_match_returns))
          (freevars_branches brs)
    | FStarC_Reflection_V2_Data.Tv_AscribedT (e1, t, tac, b) ->
        FStar_Set.union (FStar_Set.union (freevars e1) (freevars t))
          (freevars_opt tac freevars)
    | FStarC_Reflection_V2_Data.Tv_AscribedC (e1, c, tac, b) ->
        FStar_Set.union (FStar_Set.union (freevars e1) (freevars_comp c))
          (freevars_opt tac freevars)
and freevars_opt :
  'a .
    'a FStar_Pervasives_Native.option ->
      ('a -> FStarC_Reflection_V2_Data.var FStar_Set.set) ->
        FStarC_Reflection_V2_Data.var FStar_Set.set
  =
  fun o ->
    fun f ->
      match o with
      | FStar_Pervasives_Native.None -> FStar_Set.empty ()
      | FStar_Pervasives_Native.Some x -> f x
and (freevars_comp :
  FStarC_Reflection_Types.comp -> FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun c ->
    match FStarC_Reflection_V2_Builtins.inspect_comp c with
    | FStarC_Reflection_V2_Data.C_Total t -> freevars t
    | FStarC_Reflection_V2_Data.C_GTotal t -> freevars t
    | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
        FStar_Set.union (FStar_Set.union (freevars pre) (freevars post))
          (freevars pats)
    | FStarC_Reflection_V2_Data.C_Eff (us, eff_name, res, args, decrs) ->
        FStar_Set.union (FStar_Set.union (freevars res) (freevars_args args))
          (freevars_terms decrs)
and (freevars_args :
  FStarC_Reflection_V2_Data.argv Prims.list ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun ts ->
    match ts with
    | [] -> FStar_Set.empty ()
    | (t, q)::ts1 -> FStar_Set.union (freevars t) (freevars_args ts1)
and (freevars_terms :
  FStarC_Reflection_Types.term Prims.list ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun ts ->
    match ts with
    | [] -> FStar_Set.empty ()
    | t::ts1 -> FStar_Set.union (freevars t) (freevars_terms ts1)
and (freevars_binder :
  FStarC_Reflection_Types.binder ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun b ->
    let bndr = FStarC_Reflection_V2_Builtins.inspect_binder b in
    FStar_Set.union (freevars bndr.FStarC_Reflection_V2_Data.sort2)
      (freevars_terms bndr.FStarC_Reflection_V2_Data.attrs)
and (freevars_pattern :
  FStarC_Reflection_V2_Data.pattern ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun p ->
    match p with
    | FStarC_Reflection_V2_Data.Pat_Constant uu___ -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
        freevars_patterns subpats
    | FStarC_Reflection_V2_Data.Pat_Var (bv, s) -> FStar_Set.empty ()
    | FStarC_Reflection_V2_Data.Pat_Dot_Term topt ->
        freevars_opt topt freevars
and (freevars_patterns :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) Prims.list ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun ps ->
    match ps with
    | [] -> FStar_Set.empty ()
    | (p, b)::ps1 ->
        FStar_Set.union (freevars_pattern p) (freevars_patterns ps1)
and (freevars_branch :
  FStarC_Reflection_V2_Data.branch ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun br ->
    let uu___ = br in
    match uu___ with
    | (p, t) -> FStar_Set.union (freevars_pattern p) (freevars t)
and (freevars_branches :
  FStarC_Reflection_V2_Data.branch Prims.list ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun brs ->
    match brs with
    | [] -> FStar_Set.empty ()
    | hd::tl -> FStar_Set.union (freevars_branch hd) (freevars_branches tl)
and (freevars_match_returns :
  FStarC_Syntax_Syntax.match_returns_ascription ->
    FStarC_Reflection_V2_Data.var FStar_Set.set)
  =
  fun m ->
    let uu___ = m in
    match uu___ with
    | (b, (ret, as_, eq)) ->
        let b1 = freevars_binder b in
        let ret1 =
          match ret with
          | FStar_Pervasives.Inl t -> freevars t
          | FStar_Pervasives.Inr c -> freevars_comp c in
        let as_1 = freevars_opt as_ freevars in
        FStar_Set.union (FStar_Set.union b1 ret1) as_1
let rec (ln' : FStarC_Reflection_Types.term -> Prims.int -> Prims.bool) =
  fun e ->
    fun n ->
      match FStarC_Reflection_V2_Builtins.inspect_ln e with
      | FStarC_Reflection_V2_Data.Tv_UInst (uu___, uu___1) -> true
      | FStarC_Reflection_V2_Data.Tv_FVar uu___ -> true
      | FStarC_Reflection_V2_Data.Tv_Type uu___ -> true
      | FStarC_Reflection_V2_Data.Tv_Const uu___ -> true
      | FStarC_Reflection_V2_Data.Tv_Unknown -> true
      | FStarC_Reflection_V2_Data.Tv_Unsupp -> true
      | FStarC_Reflection_V2_Data.Tv_Var uu___ -> true
      | FStarC_Reflection_V2_Data.Tv_BVar m -> (bv_index m) <= n
      | FStarC_Reflection_V2_Data.Tv_App (e1, (e2, uu___)) ->
          (ln' e1 n) && (ln' e2 n)
      | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
          (ln'_binder b n) && (ln' body (n + Prims.int_one))
      | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
          (ln'_binder b n) && (ln'_comp c (n + Prims.int_one))
      | FStarC_Reflection_V2_Data.Tv_Refine (b, f) ->
          (ln'_binder b n) && (ln' f (n + Prims.int_one))
      | FStarC_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> false
      | FStarC_Reflection_V2_Data.Tv_Let (recf, attrs, b, def, body) ->
          (((ln'_terms attrs n) && (ln'_binder b n)) &&
             (if recf then ln' def (n + Prims.int_one) else ln' def n))
            && (ln' body (n + Prims.int_one))
      | FStarC_Reflection_V2_Data.Tv_Match (scr, ret, brs) ->
          ((ln' scr n) &&
             (match ret with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some m -> ln'_match_returns m n))
            && (ln'_branches brs n)
      | FStarC_Reflection_V2_Data.Tv_AscribedT (e1, t, tac, b) ->
          ((ln' e1 n) && (ln' t n)) &&
            ((match tac with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some tac1 -> ln' tac1 n))
      | FStarC_Reflection_V2_Data.Tv_AscribedC (e1, c, tac, b) ->
          ((ln' e1 n) && (ln'_comp c n)) &&
            ((match tac with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some tac1 -> ln' tac1 n))
and (ln'_comp : FStarC_Reflection_Types.comp -> Prims.int -> Prims.bool) =
  fun c ->
    fun i ->
      match FStarC_Reflection_V2_Builtins.inspect_comp c with
      | FStarC_Reflection_V2_Data.C_Total t -> ln' t i
      | FStarC_Reflection_V2_Data.C_GTotal t -> ln' t i
      | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
          ((ln' pre i) && (ln' post i)) && (ln' pats i)
      | FStarC_Reflection_V2_Data.C_Eff (us, eff_name, res, args, decrs) ->
          ((ln' res i) && (ln'_args args i)) && (ln'_terms decrs i)
and (ln'_args :
  FStarC_Reflection_V2_Data.argv Prims.list -> Prims.int -> Prims.bool) =
  fun ts ->
    fun i ->
      match ts with
      | [] -> true
      | (t, q)::ts1 -> (ln' t i) && (ln'_args ts1 i)
and (ln'_binder : FStarC_Reflection_Types.binder -> Prims.int -> Prims.bool)
  =
  fun b ->
    fun n ->
      let bndr = FStarC_Reflection_V2_Builtins.inspect_binder b in
      (ln' bndr.FStarC_Reflection_V2_Data.sort2 n) &&
        (ln'_terms bndr.FStarC_Reflection_V2_Data.attrs n)
and (ln'_terms :
  FStarC_Reflection_Types.term Prims.list -> Prims.int -> Prims.bool) =
  fun ts ->
    fun n ->
      match ts with | [] -> true | t::ts1 -> (ln' t n) && (ln'_terms ts1 n)
and (ln'_patterns :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) Prims.list ->
    Prims.int -> Prims.bool)
  =
  fun ps ->
    fun i ->
      match ps with
      | [] -> true
      | (p, b)::ps1 ->
          let b0 = ln'_pattern p i in
          let n = binder_offset_pattern p in
          let b1 = ln'_patterns ps1 (i + n) in b0 && b1
and (ln'_pattern :
  FStarC_Reflection_V2_Data.pattern -> Prims.int -> Prims.bool) =
  fun p ->
    fun i ->
      match p with
      | FStarC_Reflection_V2_Data.Pat_Constant uu___ -> true
      | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
          ln'_patterns subpats i
      | FStarC_Reflection_V2_Data.Pat_Var (bv, s) -> true
      | FStarC_Reflection_V2_Data.Pat_Dot_Term topt ->
          (match topt with
           | FStar_Pervasives_Native.None -> true
           | FStar_Pervasives_Native.Some t -> ln' t i)
and (ln'_branch :
  FStarC_Reflection_V2_Data.branch -> Prims.int -> Prims.bool) =
  fun br ->
    fun i ->
      let uu___ = br in
      match uu___ with
      | (p, t) ->
          let b = ln'_pattern p i in
          let j = binder_offset_pattern p in
          let b' = ln' t (i + j) in b && b'
and (ln'_branches :
  FStarC_Reflection_V2_Data.branch Prims.list -> Prims.int -> Prims.bool) =
  fun brs ->
    fun i ->
      match brs with
      | [] -> true
      | br::brs1 -> (ln'_branch br i) && (ln'_branches brs1 i)
and (ln'_match_returns :
  FStarC_Syntax_Syntax.match_returns_ascription -> Prims.int -> Prims.bool) =
  fun m ->
    fun i ->
      let uu___ = m in
      match uu___ with
      | (b, (ret, as_, eq)) ->
          let b1 = ln'_binder b i in
          let ret1 =
            match ret with
            | FStar_Pervasives.Inl t -> ln' t (i + Prims.int_one)
            | FStar_Pervasives.Inr c -> ln'_comp c (i + Prims.int_one) in
          let as_1 =
            match as_ with
            | FStar_Pervasives_Native.None -> true
            | FStar_Pervasives_Native.Some t -> ln' t (i + Prims.int_one) in
          (b1 && ret1) && as_1
let (ln : FStarC_Reflection_Types.term -> Prims.bool) =
  fun t -> ln' t (Prims.of_int (-1))
let (ln_comp : FStarC_Reflection_Types.comp -> Prims.bool) =
  fun c -> ln'_comp c (Prims.of_int (-1))
type term_ctxt =
  | Ctxt_hole 
  | Ctxt_app_head of term_ctxt * FStarC_Reflection_V2_Data.argv 
  | Ctxt_app_arg of FStarC_Reflection_Types.term *
  FStarC_Reflection_V2_Data.aqualv * term_ctxt 
let uu___is_Ctxt_hole uu___ =
  match uu___ with | Ctxt_hole _ -> true | _ -> false
let uu___is_Ctxt_app_head uu___ =
  match uu___ with | Ctxt_app_head _ -> true | _ -> false
let uu___is_Ctxt_app_arg uu___ =
  match uu___ with | Ctxt_app_arg _ -> true | _ -> false
let rec (apply_term_ctxt :
  term_ctxt -> FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun e ->
    fun t ->
      match e with
      | Ctxt_hole -> t
      | Ctxt_app_head (e1, arg) ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App ((apply_term_ctxt e1 t), arg))
      | Ctxt_app_arg (hd, q, e1) ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               (hd, ((apply_term_ctxt e1 t), q)))
type ('dummyV0, 'dummyV1) constant_typing =
  | CT_Unit 
  | CT_True 
  | CT_False 
let (uu___is_CT_Unit :
  FStarC_Reflection_V2_Data.vconst ->
    FStarC_Reflection_Types.term ->
      (unit, unit) constant_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | CT_Unit -> true | uu___2 -> false
let (uu___is_CT_True :
  FStarC_Reflection_V2_Data.vconst ->
    FStarC_Reflection_Types.term ->
      (unit, unit) constant_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | CT_True -> true | uu___2 -> false
let (uu___is_CT_False :
  FStarC_Reflection_V2_Data.vconst ->
    FStarC_Reflection_Types.term ->
      (unit, unit) constant_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | CT_False -> true | uu___2 -> false
type ('dummyV0, 'dummyV1) univ_eq =
  | UN_Refl of FStarC_Reflection_Types.universe 
  | UN_MaxCongL of FStarC_Reflection_Types.universe *
  FStarC_Reflection_Types.universe * FStarC_Reflection_Types.universe *
  (unit, unit) univ_eq 
  | UN_MaxCongR of FStarC_Reflection_Types.universe *
  FStarC_Reflection_Types.universe * FStarC_Reflection_Types.universe *
  (unit, unit) univ_eq 
  | UN_MaxComm of FStarC_Reflection_Types.universe *
  FStarC_Reflection_Types.universe 
  | UN_MaxLeq of FStarC_Reflection_Types.universe *
  FStarC_Reflection_Types.universe * (unit, unit) univ_leq 
and ('dummyV0, 'dummyV1) univ_leq =
  | UNLEQ_Refl of FStarC_Reflection_Types.universe 
  | UNLEQ_Succ of FStarC_Reflection_Types.universe *
  FStarC_Reflection_Types.universe * (unit, unit) univ_leq 
  | UNLEQ_Max of FStarC_Reflection_Types.universe *
  FStarC_Reflection_Types.universe 
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
let (mk_if :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun scrutinee ->
    fun then_ ->
      fun else_ ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_Match
             (scrutinee, FStar_Pervasives_Native.None,
               [((FStarC_Reflection_V2_Data.Pat_Constant
                    FStarC_Reflection_V2_Data.C_True), then_);
               ((FStarC_Reflection_V2_Data.Pat_Constant
                   FStarC_Reflection_V2_Data.C_False), else_)]))
type comp_typ =
  (FStarC_TypeChecker_Core.tot_or_ghost * FStarC_Reflection_Types.typ)
let (close_comp_typ' :
  comp_typ ->
    FStarC_Reflection_V2_Data.var ->
      Prims.nat ->
        (FStarC_TypeChecker_Core.tot_or_ghost * FStarC_Reflection_Types.term))
  =
  fun c ->
    fun x ->
      fun i ->
        ((FStar_Pervasives_Native.fst c),
          (subst_term (FStar_Pervasives_Native.snd c) [ND (x, i)]))
let (close_comp_typ :
  comp_typ ->
    FStarC_Reflection_V2_Data.var ->
      (FStarC_TypeChecker_Core.tot_or_ghost * FStarC_Reflection_Types.term))
  = fun c -> fun x -> close_comp_typ' c x Prims.int_zero
let (open_comp_typ' :
  comp_typ ->
    FStarC_Reflection_V2_Data.var ->
      Prims.nat ->
        (FStarC_TypeChecker_Core.tot_or_ghost * FStarC_Reflection_Types.term))
  =
  fun c ->
    fun x ->
      fun i ->
        ((FStar_Pervasives_Native.fst c),
          (subst_term (FStar_Pervasives_Native.snd c) (open_with_var x i)))
let (open_comp_typ :
  comp_typ ->
    FStarC_Reflection_V2_Data.var ->
      (FStarC_TypeChecker_Core.tot_or_ghost * FStarC_Reflection_Types.term))
  = fun c -> fun x -> open_comp_typ' c x Prims.int_zero
let (freevars_comp_typ :
  comp_typ -> FStarC_Reflection_V2_Data.var FStar_Set.set) =
  fun c -> freevars (FStar_Pervasives_Native.snd c)
let (mk_comp : comp_typ -> FStarC_Reflection_Types.comp) =
  fun c ->
    match FStar_Pervasives_Native.fst c with
    | FStarC_TypeChecker_Core.E_Total ->
        mk_total (FStar_Pervasives_Native.snd c)
    | FStarC_TypeChecker_Core.E_Ghost ->
        mk_ghost (FStar_Pervasives_Native.snd c)
let (mk_arrow_ct :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.aqualv ->
      comp_typ -> FStarC_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun c ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_Arrow
             ((binder_of_t_q ty qual), (mk_comp c)))
type relation =
  | R_Eq 
  | R_Sub 
let (uu___is_R_Eq : relation -> Prims.bool) =
  fun projectee -> match projectee with | R_Eq -> true | uu___ -> false
let (uu___is_R_Sub : relation -> Prims.bool) =
  fun projectee -> match projectee with | R_Sub -> true | uu___ -> false
type binding = (FStarC_Reflection_V2_Data.var * FStarC_Reflection_Types.term)
type bindings = binding Prims.list
let rename_bindings :
  'uuuuu .
    ('uuuuu * FStarC_Reflection_Types.term) Prims.list ->
      FStarC_Reflection_V2_Data.var ->
        FStarC_Reflection_V2_Data.var ->
          ('uuuuu * FStarC_Reflection_Types.term) Prims.list
  =
  fun bs ->
    fun x ->
      fun y ->
        FStar_List_Tot_Base.map
          (fun uu___ -> match uu___ with | (v, t) -> (v, (rename t x y))) bs
let rec (extend_env_l :
  FStarC_Reflection_Types.env -> bindings -> FStarC_Reflection_Types.env) =
  fun g ->
    fun bs ->
      match bs with
      | [] -> g
      | (x, t)::bs1 -> extend_env (extend_env_l g bs1) x t
let (is_non_informative_name : FStarC_Reflection_Types.name -> Prims.bool) =
  fun l ->
    ((l = FStar_Reflection_Const.unit_lid) ||
       (l = FStar_Reflection_Const.squash_qn))
      || (l = ["FStar"; "Ghost"; "erased"])
let (is_non_informative_fv : FStarC_Reflection_Types.fv -> Prims.bool) =
  fun f ->
    is_non_informative_name (FStarC_Reflection_V2_Builtins.inspect_fv f)
let rec (__close_term_vs :
  Prims.nat ->
    FStarC_Reflection_V2_Data.var Prims.list ->
      FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun i ->
    fun vs ->
      fun t ->
        match vs with
        | [] -> t
        | v::vs1 ->
            subst_term (__close_term_vs (i + Prims.int_one) vs1 t)
              [ND (v, i)]
let (close_term_vs :
  FStarC_Reflection_V2_Data.var Prims.list ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  = fun vs -> fun t -> __close_term_vs Prims.int_zero vs t
let (close_term_bs :
  binding Prims.list ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun bs ->
    fun t ->
      close_term_vs (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst bs)
        t
let (bindings_to_refl_bindings :
  binding Prims.list -> FStarC_Reflection_V2_Data.binding Prims.list) =
  fun bs ->
    FStar_List_Tot_Base.map
      (fun uu___ ->
         match uu___ with
         | (v, ty) ->
             {
               FStarC_Reflection_V2_Data.uniq1 = v;
               FStarC_Reflection_V2_Data.sort3 = ty;
               FStarC_Reflection_V2_Data.ppname3 = pp_name_default
             }) bs
let (refl_bindings_to_bindings :
  FStarC_Reflection_V2_Data.binding Prims.list -> binding Prims.list) =
  fun bs ->
    FStar_List_Tot_Base.map
      (fun b ->
         ((b.FStarC_Reflection_V2_Data.uniq1),
           (b.FStarC_Reflection_V2_Data.sort3))) bs
type ('dummyV0, 'dummyV1) non_informative =
  | Non_informative_type of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.universe 
  | Non_informative_fv of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.fv 
  | Non_informative_uinst of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.fv * FStarC_Reflection_Types.universe Prims.list 
  | Non_informative_app of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.argv * (unit,
  unit) non_informative 
  | Non_informative_total_arrow of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.aqualv *
  FStarC_Reflection_Types.term * (unit, unit) non_informative 
  | Non_informative_ghost_arrow of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.aqualv *
  FStarC_Reflection_Types.term 
  | Non_informative_token of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.typ * unit 
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
type ('bnds, 'pat, 'uuuuu) bindings_ok_for_pat = Obj.t
type ('g, 'bs, 'br) bindings_ok_for_branch = Obj.t
type ('g, 'bss, 'brs) bindings_ok_for_branch_N = Obj.t
let (binding_to_namedv :
  FStarC_Reflection_V2_Data.binding -> FStarC_Reflection_Types.namedv) =
  fun b ->
    FStarC_Reflection_V2_Builtins.pack_namedv
      {
        FStarC_Reflection_V2_Data.uniq = (b.FStarC_Reflection_V2_Data.uniq1);
        FStarC_Reflection_V2_Data.sort =
          (FStar_Sealed.seal b.FStarC_Reflection_V2_Data.sort3);
        FStarC_Reflection_V2_Data.ppname =
          (b.FStarC_Reflection_V2_Data.ppname3)
      }
let rec (elaborate_pat :
  FStarC_Reflection_V2_Data.pattern ->
    FStarC_Reflection_V2_Data.binding Prims.list ->
      (FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.binding
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun p ->
    fun bs ->
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
                (FStarC_Reflection_V2_Data.Tv_Var (binding_to_namedv b))),
              bs1)
      | (FStarC_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.Some
         t), uu___) -> FStar_Pervasives_Native.Some (t, bs)
      | (FStarC_Reflection_V2_Data.Pat_Dot_Term
         (FStar_Pervasives_Native.None), uu___) ->
          FStar_Pervasives_Native.None
      | uu___ -> FStar_Pervasives_Native.None
type ('dummyV0, 'dummyV1, 'dummyV2) typing =
  | T_Token of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  comp_typ * unit 
  | T_Var of FStarC_Reflection_Types.env * FStarC_Reflection_Types.namedv 
  | T_FVar of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv 
  | T_UInst of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv *
  FStarC_Reflection_Types.universe Prims.list 
  | T_Const of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.vconst
  * FStarC_Reflection_Types.term * (unit, unit) constant_typing 
  | T_Abs of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term * comp_typ *
  FStarC_Reflection_Types.universe * pp_name_t *
  FStarC_Reflection_V2_Data.aqualv * FStarC_TypeChecker_Core.tot_or_ghost *
  (unit, unit, unit) typing * (unit, unit, unit) typing 
  | T_App of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder *
  FStarC_Reflection_Types.term * FStarC_TypeChecker_Core.tot_or_ghost *
  (unit, unit, unit) typing * (unit, unit, unit) typing 
  | T_Let of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.typ *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.typ *
  FStarC_TypeChecker_Core.tot_or_ghost * pp_name_t * (unit, unit, unit)
  typing * (unit, unit, unit) typing 
  | T_Arrow of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.universe * FStarC_Reflection_Types.universe *
  pp_name_t * FStarC_Reflection_V2_Data.aqualv *
  FStarC_TypeChecker_Core.tot_or_ghost * FStarC_TypeChecker_Core.tot_or_ghost
  * FStarC_TypeChecker_Core.tot_or_ghost * (unit, unit, unit) typing * (
  unit, unit, unit) typing 
  | T_Refine of FStarC_Reflection_Types.env * FStarC_Reflection_V2_Data.var *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.universe * FStarC_Reflection_Types.universe *
  FStarC_TypeChecker_Core.tot_or_ghost * FStarC_TypeChecker_Core.tot_or_ghost
  * (unit, unit, unit) typing * (unit, unit, unit) typing 
  | T_PropIrrelevance of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
  FStarC_TypeChecker_Core.tot_or_ghost * FStarC_TypeChecker_Core.tot_or_ghost
  * (unit, unit, unit) typing * (unit, unit, unit) typing 
  | T_Sub of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  comp_typ * comp_typ * (unit, unit, unit) typing * (unit, unit, unit, 
  unit) related_comp 
  | T_If of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.universe *
  FStarC_Reflection_V2_Data.var * FStarC_TypeChecker_Core.tot_or_ghost *
  FStarC_TypeChecker_Core.tot_or_ghost * (unit, unit, unit) typing * (
  unit, unit, unit) typing * (unit, unit, unit) typing * (unit, unit, 
  unit) typing 
  | T_Match of FStarC_Reflection_Types.env * FStarC_Reflection_Types.universe
  * FStarC_Reflection_Types.typ * FStarC_Reflection_Types.term *
  FStarC_TypeChecker_Core.tot_or_ghost * (unit, unit, unit) typing *
  FStarC_TypeChecker_Core.tot_or_ghost * (unit, unit, unit) typing *
  FStarC_Reflection_V2_Data.branch Prims.list * comp_typ *
  FStarC_Reflection_V2_Data.binding Prims.list Prims.list * (unit, unit,
  unit, unit, unit) match_is_complete * (unit, unit, unit, unit, unit, 
  unit, unit) branches_typing 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3) related =
  | Rel_refl of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  relation 
  | Rel_sym of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * (unit, unit, unit, unit) related 
  | Rel_trans of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term * relation *
  (unit, unit, unit, unit) related * (unit, unit, unit, unit) related 
  | Rel_univ of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.universe * FStarC_Reflection_Types.universe *
  (unit, unit) univ_eq 
  | Rel_beta of FStarC_Reflection_Types.env * FStarC_Reflection_Types.typ *
  FStarC_Reflection_V2_Data.aqualv * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term 
  | Rel_eq_token of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term * unit 
  | Rel_subtyping_token of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term * unit 
  | Rel_equiv of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * relation * (unit, unit, unit, unit) related
  
  | Rel_arrow of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.aqualv * comp_typ
  * comp_typ * relation * FStarC_Reflection_V2_Data.var * (unit, unit, 
  unit, unit) related * (unit, unit, unit, unit) related_comp 
  | Rel_abs of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.aqualv *
  FStarC_Reflection_Types.term * FStarC_Reflection_Types.term *
  FStarC_Reflection_V2_Data.var * (unit, unit, unit, unit) related * (
  unit, unit, unit, unit) related 
  | Rel_ctxt of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * term_ctxt * (unit, unit, unit, unit) related 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3) related_comp =
  | Relc_typ of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term * FStarC_TypeChecker_Core.tot_or_ghost *
  relation * (unit, unit, unit, unit) related 
  | Relc_total_ghost of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term 
  | Relc_ghost_total of FStarC_Reflection_Types.env *
  FStarC_Reflection_Types.term * (unit, unit) non_informative 
and ('g, 'scuu, 'scuty, 'sc, 'rty, 'dummyV0, 'dummyV1) branches_typing =
  | BT_Nil 
  | BT_S of FStarC_Reflection_V2_Data.branch *
  FStarC_Reflection_V2_Data.binding Prims.list * (unit, unit, unit, unit,
  unit, unit, unit) branch_typing * FStarC_Reflection_V2_Data.branch
  Prims.list * FStarC_Reflection_V2_Data.binding Prims.list Prims.list *
  (unit, unit, unit, unit, unit, unit, unit) branches_typing 
and ('g, 'scuu, 'scuty, 'sc, 'rty, 'dummyV0, 'dummyV1) branch_typing =
  | BO of FStarC_Reflection_V2_Data.pattern *
  FStarC_Reflection_V2_Data.binding Prims.list *
  FStarC_Reflection_V2_Data.var * FStarC_Reflection_Types.term * unit *
  (unit, unit, unit) typing 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3, 'dummyV4) match_is_complete =
  | MC_Tok of FStarC_Reflection_Types.env * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.typ * FStarC_Reflection_V2_Data.pattern Prims.list
  * FStarC_Reflection_V2_Data.binding Prims.list Prims.list * unit 
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
type ('g, 't1, 't2) sub_typing = (unit, unit, unit, unit) related
type ('g, 'c1, 'c2) sub_comp = (unit, unit, unit, unit) related_comp
type ('g, 't1, 't2) equiv = (unit, unit, unit, unit) related
type ('g, 'e, 't) tot_typing = (unit, unit, unit) typing
type ('g, 'e, 't) ghost_typing = (unit, unit, unit) typing
let (subtyping_token_renaming :
  FStarC_Reflection_Types.env ->
    bindings ->
      bindings ->
        FStarC_Reflection_V2_Data.var ->
          FStarC_Reflection_V2_Data.var ->
            FStarC_Reflection_Types.term ->
              FStarC_Reflection_Types.term ->
                FStarC_Reflection_Types.term ->
                  (unit, unit, unit) FStarC_Tactics_Types.subtyping_token ->
                    (unit, unit, unit) FStarC_Tactics_Types.subtyping_token)
  =
  fun g ->
    fun bs0 ->
      fun bs1 ->
        fun x ->
          fun y -> fun t -> fun t0 -> fun t1 -> fun d -> Prims.magic ()
let (subtyping_token_weakening :
  FStarC_Reflection_Types.env ->
    bindings ->
      bindings ->
        FStarC_Reflection_V2_Data.var ->
          FStarC_Reflection_Types.term ->
            FStarC_Reflection_Types.term ->
              FStarC_Reflection_Types.term ->
                (unit, unit, unit) FStarC_Tactics_Types.subtyping_token ->
                  (unit, unit, unit) FStarC_Tactics_Types.subtyping_token)
  =
  fun g ->
    fun bs0 ->
      fun bs1 ->
        fun x -> fun t -> fun t0 -> fun t1 -> fun d -> Prims.magic ()
let (simplify_umax :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.universe ->
        (unit, unit, unit) typing -> (unit, unit, unit) typing)
  =
  fun g ->
    fun t ->
      fun u ->
        fun d ->
          let ue = UN_MaxLeq (u, u, (UNLEQ_Refl u)) in
          let du = Rel_univ (g, (u_max u u), u, ue) in
          let du1 =
            Rel_equiv (g, (tm_type (u_max u u)), (tm_type u), R_Sub, du) in
          T_Sub
            (g, t, (FStarC_TypeChecker_Core.E_Total, (tm_type (u_max u u))),
              (FStarC_TypeChecker_Core.E_Total, (tm_type u)), d,
              (Relc_typ
                 (g, (tm_type (u_max u u)), (tm_type u),
                   FStarC_TypeChecker_Core.E_Total, R_Sub, du1)))
let (equiv_arrow :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.typ ->
          FStarC_Reflection_V2_Data.aqualv ->
            FStarC_Reflection_V2_Data.var ->
              (unit, unit, unit) equiv -> (unit, unit, unit) equiv)
  =
  fun g ->
    fun e1 ->
      fun e2 ->
        fun ty ->
          fun q ->
            fun x ->
              fun eq ->
                let c1 = (FStarC_TypeChecker_Core.E_Total, e1) in
                let c2 = (FStarC_TypeChecker_Core.E_Total, e2) in
                Rel_arrow
                  (g, ty, ty, q, c1, c2, R_Eq, x, (Rel_refl (g, ty, R_Eq)),
                    (Relc_typ
                       ((extend_env g x ty),
                         (subst_term e1 (open_with_var x Prims.int_zero)),
                         (subst_term e2 (open_with_var x Prims.int_zero)),
                         (FStar_Pervasives_Native.fst c1), R_Eq, eq)))
let (equiv_abs_close :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.typ ->
          FStarC_Reflection_V2_Data.aqualv ->
            FStarC_Reflection_V2_Data.var ->
              (unit, unit, unit) equiv -> (unit, unit, unit) equiv)
  =
  fun g ->
    fun e1 ->
      fun e2 ->
        fun ty ->
          fun q ->
            fun x ->
              fun eq ->
                let eq1 = eq in
                Rel_abs
                  (g, ty, ty, q, (subst_term e1 [ND (x, Prims.int_zero)]),
                    (subst_term e2 [ND (x, Prims.int_zero)]), x,
                    (Rel_refl (g, ty, R_Eq)), eq1)
type 'g fstar_env_fvs = unit
type fstar_env = FStarC_Reflection_Types.env
type fstar_top_env = fstar_env
type ('dummyV0, 'dummyV1) sigelt_typing =
  | ST_Let of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv *
  FStarC_Reflection_Types.typ * FStarC_Reflection_Types.term * unit 
  | ST_Let_Opaque of FStarC_Reflection_Types.env * FStarC_Reflection_Types.fv
  * FStarC_Reflection_Types.typ * unit 
let (uu___is_ST_Let :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ST_Let (g, fv, ty, tm, _4) -> true
        | uu___2 -> false
let (__proj__ST_Let__item__g :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> FStarC_Reflection_Types.env)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | ST_Let (g, fv, ty, tm, _4) -> g
let (__proj__ST_Let__item__fv :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> FStarC_Reflection_Types.fv)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ST_Let (g, fv, ty, tm, _4) -> fv
let (__proj__ST_Let__item__ty :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> FStarC_Reflection_Types.typ)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ST_Let (g, fv, ty, tm, _4) -> ty
let (__proj__ST_Let__item__tm :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> FStarC_Reflection_Types.term)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ST_Let (g, fv, ty, tm, _4) -> tm
let (uu___is_ST_Let_Opaque :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | ST_Let_Opaque (g, fv, ty, _3) -> true
        | uu___2 -> false
let (__proj__ST_Let_Opaque__item__g :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> FStarC_Reflection_Types.env)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ST_Let_Opaque (g, fv, ty, _3) -> g
let (__proj__ST_Let_Opaque__item__fv :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> FStarC_Reflection_Types.fv)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ST_Let_Opaque (g, fv, ty, _3) -> fv
let (__proj__ST_Let_Opaque__item__ty :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.sigelt ->
      (unit, unit) sigelt_typing -> FStarC_Reflection_Types.typ)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | ST_Let_Opaque (g, fv, ty, _3) -> ty
type blob = (Prims.string * FStarC_Reflection_Types.term)
type ('s, 't) sigelt_has_type = Obj.t
type ('g, 't) sigelt_for =
  (Prims.bool * FStarC_Reflection_Types.sigelt * blob
    FStar_Pervasives_Native.option)
type ('g, 't) dsl_tac_result_t =
  ((unit, unit) sigelt_for Prims.list * (unit, unit) sigelt_for * (unit,
    unit) sigelt_for Prims.list)
type dsl_tac_t =
  (fstar_top_env * FStarC_Reflection_Types.typ
    FStar_Pervasives_Native.option) ->
    ((unit, unit) dsl_tac_result_t, unit) FStar_Tactics_Effect.tac_repr
let (if_complete_match :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      (unit, unit, unit, unit, unit)
        FStarC_Tactics_V2_Builtins.match_complete_token)
  = fun g -> fun t -> Prims.magic ()
let (mkif :
  fstar_env ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.term ->
          FStarC_Reflection_Types.term ->
            FStarC_Reflection_Types.universe ->
              FStarC_Reflection_V2_Data.var ->
                FStarC_TypeChecker_Core.tot_or_ghost ->
                  FStarC_TypeChecker_Core.tot_or_ghost ->
                    (unit, unit, unit) typing ->
                      (unit, unit, unit) typing ->
                        (unit, unit, unit) typing ->
                          (unit, unit, unit) typing ->
                            (unit, unit, unit) typing)
  =
  fun g ->
    fun scrutinee ->
      fun then_ ->
        fun else_ ->
          fun ty ->
            fun u_ty ->
              fun hyp ->
                fun eff ->
                  fun ty_eff ->
                    fun ts ->
                      fun tt ->
                        fun te ->
                          fun tr ->
                            let brt =
                              ((FStarC_Reflection_V2_Data.Pat_Constant
                                  FStarC_Reflection_V2_Data.C_True), then_) in
                            let bre =
                              ((FStarC_Reflection_V2_Data.Pat_Constant
                                  FStarC_Reflection_V2_Data.C_False), else_) in
                            let brty uu___ =
                              BT_S
                                (((FStarC_Reflection_V2_Data.Pat_Constant
                                     FStarC_Reflection_V2_Data.C_True),
                                   then_), [],
                                  (BO
                                     ((FStarC_Reflection_V2_Data.Pat_Constant
                                         FStarC_Reflection_V2_Data.C_True),
                                       [], hyp, then_, (), tt)),
                                  [((FStarC_Reflection_V2_Data.Pat_Constant
                                       FStarC_Reflection_V2_Data.C_False),
                                     else_)], [[]],
                                  (BT_S
                                     (((FStarC_Reflection_V2_Data.Pat_Constant
                                          FStarC_Reflection_V2_Data.C_False),
                                        else_), [],
                                       (BO
                                          ((FStarC_Reflection_V2_Data.Pat_Constant
                                              FStarC_Reflection_V2_Data.C_False),
                                            [], hyp, else_, (), te)), [], [],
                                       BT_Nil))) in
                            T_Match
                              (g, u_zero, bool_ty, scrutinee,
                                FStarC_TypeChecker_Core.E_Total,
                                (T_FVar (g, bool_fv)), eff, ts, [brt; bre],
                                (eff, ty), [[]; []],
                                (MC_Tok
                                   (g, scrutinee, bool_ty,
                                     (FStar_List_Tot_Base.map
                                        FStar_Pervasives_Native.fst
                                        [brt; bre]), [[]; []], ())),
                                (brty ()))
let (mk_checked_let :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.name ->
      Prims.string ->
        FStarC_Reflection_Types.term ->
          FStarC_Reflection_Types.typ -> (unit, unit) sigelt_for)
  =
  fun g ->
    fun cur_module ->
      fun nm ->
        fun tm ->
          fun ty ->
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
            let pf = ST_Let (g, fv, ty, tm, ()) in
            (true, se, FStar_Pervasives_Native.None)
let (mk_unchecked_let :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.name ->
      Prims.string ->
        FStarC_Reflection_Types.term ->
          FStarC_Reflection_Types.typ ->
            (Prims.bool * FStarC_Reflection_Types.sigelt * blob
              FStar_Pervasives_Native.option))
  =
  fun g ->
    fun cur_module ->
      fun nm ->
        fun tm ->
          fun ty ->
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
let (typing_to_token :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      comp_typ ->
        (unit, unit, unit) typing ->
          (unit, unit, unit) FStarC_Tactics_Types.typing_token)
  = fun g -> fun e -> fun c -> fun uu___ -> Prims.magic ()