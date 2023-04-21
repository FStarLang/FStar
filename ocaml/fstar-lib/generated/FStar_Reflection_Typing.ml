open Prims
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
let (mk_binder :
  pp_name_t ->
    FStar_Reflection_Data.var ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Data.aqualv -> FStar_Reflection_Types.binder)
  =
  fun pp_name ->
    fun x ->
      fun ty ->
        fun q ->
          FStar_Reflection_Builtins.pack_binder
            {
              FStar_Reflection_Data.binder_bv =
                (FStar_Reflection_Builtins.pack_bv
                   {
                     FStar_Reflection_Data.bv_ppname = pp_name;
                     FStar_Reflection_Data.bv_index = x;
                     FStar_Reflection_Data.bv_sort = ty
                   });
              FStar_Reflection_Data.binder_qual = q;
              FStar_Reflection_Data.binder_attrs = []
            }
let (extend_env :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Data.var ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.env)
  =
  fun e ->
    fun x ->
      fun ty ->
        FStar_Reflection_Builtins.push_binder e
          (mk_binder (seal_pp_name "x") x ty FStar_Reflection_Data.Q_Explicit)
let (as_binder :
  FStar_Reflection_Data.var ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.binder)
  =
  fun x ->
    fun ty ->
      mk_binder (seal_pp_name "x") x ty FStar_Reflection_Data.Q_Explicit
let (bv_index : FStar_Reflection_Types.bv -> FStar_Reflection_Data.var) =
  fun x ->
    (FStar_Reflection_Builtins.inspect_bv x).FStar_Reflection_Data.bv_index
let (binder_sort :
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.typ) =
  fun b ->
    let uu___ = FStar_Reflection_Builtins.inspect_binder b in
    match uu___ with
    | { FStar_Reflection_Data.binder_bv = bv;
        FStar_Reflection_Data.binder_qual = uu___1;
        FStar_Reflection_Data.binder_attrs = uu___2;_} ->
        (FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_sort
let (binder_qual :
  FStar_Reflection_Types.binder -> FStar_Reflection_Data.aqualv) =
  fun b ->
    let uu___ = FStar_Reflection_Builtins.inspect_binder b in
    match uu___ with
    | { FStar_Reflection_Data.binder_bv = uu___1;
        FStar_Reflection_Data.binder_qual = q;
        FStar_Reflection_Data.binder_attrs = uu___2;_} -> q
type open_or_close =
  | OpenWith of FStar_Reflection_Types.term 
  | CloseVar of FStar_Reflection_Data.var 
  | Rename of FStar_Reflection_Data.var * FStar_Reflection_Data.var 
let (uu___is_OpenWith : open_or_close -> Prims.bool) =
  fun projectee ->
    match projectee with | OpenWith _0 -> true | uu___ -> false
let (__proj__OpenWith__item___0 :
  open_or_close -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | OpenWith _0 -> _0
let (uu___is_CloseVar : open_or_close -> Prims.bool) =
  fun projectee ->
    match projectee with | CloseVar _0 -> true | uu___ -> false
let (__proj__CloseVar__item___0 : open_or_close -> FStar_Reflection_Data.var)
  = fun projectee -> match projectee with | CloseVar _0 -> _0
let (uu___is_Rename : open_or_close -> Prims.bool) =
  fun projectee ->
    match projectee with | Rename (_0, _1) -> true | uu___ -> false
let (__proj__Rename__item___0 : open_or_close -> FStar_Reflection_Data.var) =
  fun projectee -> match projectee with | Rename (_0, _1) -> _0
let (__proj__Rename__item___1 : open_or_close -> FStar_Reflection_Data.var) =
  fun projectee -> match projectee with | Rename (_0, _1) -> _1
let (tun : FStar_Reflection_Types.term) =
  FStar_Reflection_Builtins.pack_ln FStar_Reflection_Data.Tv_Unknown
let (make_bv :
  Prims.nat -> FStar_Reflection_Types.term -> FStar_Reflection_Data.bv_view)
  =
  fun n ->
    fun t ->
      {
        FStar_Reflection_Data.bv_ppname = pp_name_default;
        FStar_Reflection_Data.bv_index = n;
        FStar_Reflection_Data.bv_sort = t
      }
let (make_bv_with_name :
  pp_name_t ->
    Prims.nat -> FStar_Reflection_Types.term -> FStar_Reflection_Data.bv_view)
  =
  fun s ->
    fun n ->
      fun t ->
        {
          FStar_Reflection_Data.bv_ppname = s;
          FStar_Reflection_Data.bv_index = n;
          FStar_Reflection_Data.bv_sort = t
        }
let (var_as_bv : Prims.nat -> FStar_Reflection_Types.bv) =
  fun v -> FStar_Reflection_Builtins.pack_bv (make_bv v tun)
let (var_as_term : FStar_Reflection_Data.var -> FStar_Reflection_Types.term)
  =
  fun v ->
    FStar_Reflection_Builtins.pack_ln
      (FStar_Reflection_Data.Tv_Var (var_as_bv v))
let (binder_of_t_q :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.aqualv -> FStar_Reflection_Types.binder)
  = fun t -> fun q -> mk_binder pp_name_default Prims.int_zero t q
let (mk_abs :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.aqualv ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun qual ->
      fun t ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Abs ((binder_of_t_q ty qual), t))
let (bound_var : Prims.nat -> FStar_Reflection_Types.term) =
  fun i ->
    FStar_Reflection_Builtins.pack_ln
      (FStar_Reflection_Data.Tv_BVar
         (FStar_Reflection_Builtins.pack_bv (make_bv i tun)))
let (open_with_var : FStar_Reflection_Data.var -> open_or_close) =
  fun x ->
    OpenWith
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_Var (var_as_bv x)))
let (maybe_index_of_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.var FStar_Pervasives_Native.option)
  =
  fun x ->
    match FStar_Reflection_Builtins.inspect_ln x with
    | FStar_Reflection_Data.Tv_Var bv ->
        FStar_Pervasives_Native.Some (bv_index bv)
    | uu___ -> FStar_Pervasives_Native.None
let (open_or_close_ctx_uvar_and_subst :
  FStar_Reflection_Types.ctx_uvar_and_subst ->
    open_or_close -> Prims.nat -> FStar_Reflection_Types.ctx_uvar_and_subst)
  = fun c -> fun v -> fun i -> Prims.magic ()
let rec (binder_offset_patterns :
  (FStar_Reflection_Data.pattern * Prims.bool) Prims.list -> Prims.nat) =
  fun ps ->
    match ps with
    | [] -> Prims.int_zero
    | (p, b)::ps1 ->
        let n = binder_offset_pattern p in
        let m = binder_offset_patterns ps1 in n + m
and (binder_offset_pattern : FStar_Reflection_Data.pattern -> Prims.nat) =
  fun p ->
    match p with
    | FStar_Reflection_Data.Pat_Constant uu___ -> Prims.int_zero
    | FStar_Reflection_Data.Pat_Dot_Term uu___ -> Prims.int_zero
    | FStar_Reflection_Data.Pat_Var uu___ -> Prims.int_one
    | FStar_Reflection_Data.Pat_Wild uu___ -> Prims.int_one
    | FStar_Reflection_Data.Pat_Cons (fv, us, pats) ->
        binder_offset_patterns pats
let rec (open_or_close_term' :
  FStar_Reflection_Types.term ->
    open_or_close -> Prims.nat -> FStar_Reflection_Types.term)
  =
  fun t ->
    fun v ->
      fun i ->
        match FStar_Reflection_Builtins.inspect_ln t with
        | FStar_Reflection_Data.Tv_UInst (uu___, uu___1) -> t
        | FStar_Reflection_Data.Tv_FVar uu___ -> t
        | FStar_Reflection_Data.Tv_Type uu___ -> t
        | FStar_Reflection_Data.Tv_Const uu___ -> t
        | FStar_Reflection_Data.Tv_Unknown -> t
        | FStar_Reflection_Data.Tv_Var x ->
            (match v with
             | OpenWith uu___ -> t
             | CloseVar y ->
                 if (bv_index x) = y
                 then
                   FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_BVar
                        (FStar_Reflection_Builtins.pack_bv
                           (let uu___ =
                              FStar_Reflection_Builtins.inspect_bv x in
                            {
                              FStar_Reflection_Data.bv_ppname =
                                (uu___.FStar_Reflection_Data.bv_ppname);
                              FStar_Reflection_Data.bv_index = i;
                              FStar_Reflection_Data.bv_sort =
                                (uu___.FStar_Reflection_Data.bv_sort)
                            })))
                 else t
             | Rename (y, z) ->
                 if (bv_index x) = y
                 then
                   FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_Var
                        (FStar_Reflection_Builtins.pack_bv
                           (let uu___ =
                              FStar_Reflection_Builtins.inspect_bv x in
                            {
                              FStar_Reflection_Data.bv_ppname =
                                (uu___.FStar_Reflection_Data.bv_ppname);
                              FStar_Reflection_Data.bv_index = z;
                              FStar_Reflection_Data.bv_sort =
                                (uu___.FStar_Reflection_Data.bv_sort)
                            })))
                 else t)
        | FStar_Reflection_Data.Tv_BVar j ->
            (match v with
             | Rename (uu___, uu___1) -> t
             | CloseVar uu___ -> t
             | OpenWith v1 ->
                 if i = (bv_index j)
                 then
                   (match maybe_index_of_term v1 with
                    | FStar_Pervasives_Native.None -> v1
                    | FStar_Pervasives_Native.Some k ->
                        FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_Var
                             (FStar_Reflection_Builtins.pack_bv
                                (let uu___ =
                                   FStar_Reflection_Builtins.inspect_bv j in
                                 {
                                   FStar_Reflection_Data.bv_ppname =
                                     (uu___.FStar_Reflection_Data.bv_ppname);
                                   FStar_Reflection_Data.bv_index = k;
                                   FStar_Reflection_Data.bv_sort =
                                     (uu___.FStar_Reflection_Data.bv_sort)
                                 }))))
                 else t)
        | FStar_Reflection_Data.Tv_App (hd, argv) ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_App
                 ((open_or_close_term' hd v i),
                   ((open_or_close_term' (FStar_Pervasives_Native.fst argv) v
                       i), (FStar_Pervasives_Native.snd argv))))
        | FStar_Reflection_Data.Tv_Abs (b, body) ->
            let b' = open_or_close_binder' b v i in
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_Abs
                 (b', (open_or_close_term' body v (i + Prims.int_one))))
        | FStar_Reflection_Data.Tv_Arrow (b, c) ->
            let b' = open_or_close_binder' b v i in
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_Arrow
                 (b', (open_or_close_comp' c v (i + Prims.int_one))))
        | FStar_Reflection_Data.Tv_Refine (bv, f) ->
            let bv' = open_or_close_bv' bv v i in
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_Refine
                 (bv', (open_or_close_term' f v (i + Prims.int_one))))
        | FStar_Reflection_Data.Tv_Uvar (j, c) ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_Uvar
                 (j, (open_or_close_ctx_uvar_and_subst c v i)))
        | FStar_Reflection_Data.Tv_Let (recf, attrs, bv, def, body) ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_Let
                 (recf, (open_or_close_terms' attrs v i),
                   (open_or_close_bv' bv v i),
                   (if recf
                    then open_or_close_term' def v (i + Prims.int_one)
                    else open_or_close_term' def v i),
                   (open_or_close_term' body v (i + Prims.int_one))))
        | FStar_Reflection_Data.Tv_Match (scr, ret, brs) ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_Match
                 ((open_or_close_term' scr v i),
                   (match ret with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some m ->
                        FStar_Pervasives_Native.Some
                          (open_or_close_match_returns' m v i)),
                   (open_or_close_branches' brs v i)))
        | FStar_Reflection_Data.Tv_AscribedT (e, t1, tac, b) ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_AscribedT
                 ((open_or_close_term' e v i), (open_or_close_term' t1 v i),
                   (match tac with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some tac1 ->
                        FStar_Pervasives_Native.Some
                          (open_or_close_term' tac1 v i)), b))
        | FStar_Reflection_Data.Tv_AscribedC (e, c, tac, b) ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_AscribedC
                 ((open_or_close_term' e v i), (open_or_close_comp' c v i),
                   (match tac with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some tac1 ->
                        FStar_Pervasives_Native.Some
                          (open_or_close_term' tac1 v i)), b))
and (open_or_close_bv' :
  FStar_Reflection_Types.bv ->
    open_or_close -> Prims.nat -> FStar_Reflection_Types.bv)
  =
  fun b ->
    fun v ->
      fun i ->
        let bv = FStar_Reflection_Builtins.inspect_bv b in
        FStar_Reflection_Builtins.pack_bv
          {
            FStar_Reflection_Data.bv_ppname =
              (bv.FStar_Reflection_Data.bv_ppname);
            FStar_Reflection_Data.bv_index =
              (bv.FStar_Reflection_Data.bv_index);
            FStar_Reflection_Data.bv_sort =
              (open_or_close_term' bv.FStar_Reflection_Data.bv_sort v i)
          }
and (open_or_close_binder' :
  FStar_Reflection_Types.binder ->
    open_or_close -> Prims.nat -> FStar_Reflection_Types.binder)
  =
  fun b ->
    fun v ->
      fun i ->
        let bndr = FStar_Reflection_Builtins.inspect_binder b in
        FStar_Reflection_Builtins.pack_binder
          {
            FStar_Reflection_Data.binder_bv =
              (open_or_close_bv' bndr.FStar_Reflection_Data.binder_bv v i);
            FStar_Reflection_Data.binder_qual =
              (bndr.FStar_Reflection_Data.binder_qual);
            FStar_Reflection_Data.binder_attrs =
              (open_or_close_terms' bndr.FStar_Reflection_Data.binder_attrs v
                 i)
          }
and (open_or_close_comp' :
  FStar_Reflection_Types.comp ->
    open_or_close -> Prims.nat -> FStar_Reflection_Types.comp)
  =
  fun c ->
    fun v ->
      fun i ->
        match FStar_Reflection_Builtins.inspect_comp c with
        | FStar_Reflection_Data.C_Total t ->
            FStar_Reflection_Builtins.pack_comp
              (FStar_Reflection_Data.C_Total (open_or_close_term' t v i))
        | FStar_Reflection_Data.C_GTotal t ->
            FStar_Reflection_Builtins.pack_comp
              (FStar_Reflection_Data.C_GTotal (open_or_close_term' t v i))
        | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
            FStar_Reflection_Builtins.pack_comp
              (FStar_Reflection_Data.C_Lemma
                 ((open_or_close_term' pre v i),
                   (open_or_close_term' post v i),
                   (open_or_close_term' pats v i)))
        | FStar_Reflection_Data.C_Eff (us, eff_name, res, args, decrs) ->
            FStar_Reflection_Builtins.pack_comp
              (FStar_Reflection_Data.C_Eff
                 (us, eff_name, (open_or_close_term' res v i),
                   (open_or_close_args' args v i),
                   (open_or_close_terms' decrs v i)))
and (open_or_close_terms' :
  FStar_Reflection_Types.term Prims.list ->
    open_or_close -> Prims.nat -> FStar_Reflection_Types.term Prims.list)
  =
  fun ts ->
    fun v ->
      fun i ->
        match ts with
        | [] -> []
        | t::ts1 -> (open_or_close_term' t v i) ::
            (open_or_close_terms' ts1 v i)
and (open_or_close_args' :
  FStar_Reflection_Data.argv Prims.list ->
    open_or_close -> Prims.nat -> FStar_Reflection_Data.argv Prims.list)
  =
  fun ts ->
    fun v ->
      fun i ->
        match ts with
        | [] -> []
        | (t, q)::ts1 -> ((open_or_close_term' t v i), q) ::
            (open_or_close_args' ts1 v i)
and (open_or_close_patterns' :
  (FStar_Reflection_Data.pattern * Prims.bool) Prims.list ->
    open_or_close ->
      Prims.nat -> (FStar_Reflection_Data.pattern * Prims.bool) Prims.list)
  =
  fun ps ->
    fun v ->
      fun i ->
        match ps with
        | [] -> ps
        | (p, b)::ps1 ->
            let n = binder_offset_pattern p in
            let p1 = open_or_close_pattern' p v i in
            let ps2 = open_or_close_patterns' ps1 v (i + n) in (p1, b) :: ps2
and (open_or_close_pattern' :
  FStar_Reflection_Data.pattern ->
    open_or_close -> Prims.nat -> FStar_Reflection_Data.pattern)
  =
  fun p ->
    fun v ->
      fun i ->
        match p with
        | FStar_Reflection_Data.Pat_Constant uu___ -> p
        | FStar_Reflection_Data.Pat_Cons (fv, us, pats) ->
            let pats1 = open_or_close_patterns' pats v i in
            FStar_Reflection_Data.Pat_Cons (fv, us, pats1)
        | FStar_Reflection_Data.Pat_Var bv ->
            FStar_Reflection_Data.Pat_Var (open_or_close_bv' bv v i)
        | FStar_Reflection_Data.Pat_Wild bv ->
            FStar_Reflection_Data.Pat_Wild (open_or_close_bv' bv v i)
        | FStar_Reflection_Data.Pat_Dot_Term topt ->
            FStar_Reflection_Data.Pat_Dot_Term
              ((match topt with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some t ->
                    FStar_Pervasives_Native.Some (open_or_close_term' t v i)))
and (open_or_close_branch' :
  FStar_Reflection_Data.branch ->
    open_or_close -> Prims.nat -> FStar_Reflection_Data.branch)
  =
  fun br ->
    fun v ->
      fun i ->
        let uu___ = br in
        match uu___ with
        | (p, t) ->
            let p1 = open_or_close_pattern' p v i in
            let j = binder_offset_pattern p1 in
            let t1 = open_or_close_term' t v (i + j) in (p1, t1)
and (open_or_close_branches' :
  FStar_Reflection_Data.branch Prims.list ->
    open_or_close -> Prims.nat -> FStar_Reflection_Data.branch Prims.list)
  =
  fun brs ->
    fun v ->
      fun i ->
        match brs with
        | [] -> []
        | br::brs1 -> (open_or_close_branch' br v i) ::
            (open_or_close_branches' brs1 v i)
and (open_or_close_match_returns' :
  FStar_Reflection_Types.match_returns_ascription ->
    open_or_close ->
      Prims.nat -> FStar_Reflection_Types.match_returns_ascription)
  =
  fun m ->
    fun v ->
      fun i ->
        let uu___ = m in
        match uu___ with
        | (b, (ret, as_, eq)) ->
            let b1 = open_or_close_binder' b v i in
            let ret1 =
              match ret with
              | FStar_Pervasives.Inl t ->
                  FStar_Pervasives.Inl
                    (open_or_close_term' t v (i + Prims.int_one))
              | FStar_Pervasives.Inr c ->
                  FStar_Pervasives.Inr
                    (open_or_close_comp' c v (i + Prims.int_one)) in
            let as_1 =
              match as_ with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some t ->
                  FStar_Pervasives_Native.Some
                    (open_or_close_term' t v (i + Prims.int_one)) in
            (b1, (ret1, as_1, eq))
let (open_with :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.open_with t v
let (open_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.var -> FStar_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.open_term t v
let (close_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.var -> FStar_Reflection_Types.term)
  = fun t -> fun v -> FStar_Reflection_Typing_Builtins.close_term t v
let (rename :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.var ->
      FStar_Reflection_Data.var -> FStar_Reflection_Types.term)
  = fun t -> fun x -> fun y -> FStar_Reflection_Typing_Builtins.rename t x y
let (bv_as_binder :
  FStar_Reflection_Types.bv -> FStar_Reflection_Types.binder) =
  fun bv ->
    FStar_Reflection_Builtins.pack_binder
      {
        FStar_Reflection_Data.binder_bv = bv;
        FStar_Reflection_Data.binder_qual = FStar_Reflection_Data.Q_Explicit;
        FStar_Reflection_Data.binder_attrs = []
      }
let (constant_as_term :
  FStar_Reflection_Data.vconst -> FStar_Reflection_Types.term) =
  fun v ->
    FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_Const v)
let (unit_exp : FStar_Reflection_Types.term) =
  constant_as_term FStar_Reflection_Data.C_Unit
let (unit_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.unit_lid
let (unit_ty : FStar_Reflection_Types.term) =
  FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_FVar unit_fv)
let (bool_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.bool_lid
let (bool_ty : FStar_Reflection_Types.term) =
  FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_FVar bool_fv)
let (u_zero : FStar_Reflection_Types.universe) =
  FStar_Reflection_Builtins.pack_universe FStar_Reflection_Data.Uv_Zero
let (u_max :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe -> FStar_Reflection_Types.universe)
  =
  fun u1 ->
    fun u2 ->
      FStar_Reflection_Builtins.pack_universe
        (FStar_Reflection_Data.Uv_Max [u1; u2])
let (u_succ :
  FStar_Reflection_Types.universe -> FStar_Reflection_Types.universe) =
  fun u ->
    FStar_Reflection_Builtins.pack_universe (FStar_Reflection_Data.Uv_Succ u)
let (mk_total : FStar_Reflection_Types.typ -> FStar_Reflection_Types.comp) =
  fun t ->
    FStar_Reflection_Builtins.pack_comp (FStar_Reflection_Data.C_Total t)
let (tm_type :
  FStar_Reflection_Types.universe -> FStar_Reflection_Types.term) =
  fun u ->
    FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_Type u)
let (tm_prop : FStar_Reflection_Types.term) =
  let prop_fv =
    FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.prop_qn in
  FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_FVar prop_fv)
let (eqtype_lid : FStar_Reflection_Types.name) = ["Prims"; "eqtype"]
let (true_bool : FStar_Reflection_Types.term) =
  FStar_Reflection_Builtins.pack_ln
    (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_True)
let (false_bool : FStar_Reflection_Types.term) =
  FStar_Reflection_Builtins.pack_ln
    (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_False)
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
            FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq2_qn in
          let eq22 =
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_UInst (eq21, [u])) in
          let h =
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_App
                 (eq22, (t, FStar_Reflection_Data.Q_Implicit))) in
          let h1 =
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_App
                 (h, (v0, FStar_Reflection_Data.Q_Explicit))) in
          let h2 =
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_App
                 (h1, (v1, FStar_Reflection_Data.Q_Explicit))) in
          h2
let (b2t_lid : FStar_Reflection_Types.name) = ["Prims"; "b2t"]
let (b2t_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_Builtins.pack_fv b2t_lid
let (b2t_ty : FStar_Reflection_Types.term) =
  FStar_Reflection_Builtins.pack_ln
    (FStar_Reflection_Data.Tv_Arrow
       ((as_binder Prims.int_zero bool_ty), (mk_total (tm_type u_zero))))
let rec (freevars :
  FStar_Reflection_Types.term -> FStar_Reflection_Data.var FStar_Set.set) =
  fun e ->
    match FStar_Reflection_Builtins.inspect_ln e with
    | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) ->
        FStar_Set.complement (FStar_Set.empty ())
    | FStar_Reflection_Data.Tv_UInst (uu___, uu___1) -> FStar_Set.empty ()
    | FStar_Reflection_Data.Tv_FVar uu___ -> FStar_Set.empty ()
    | FStar_Reflection_Data.Tv_Type uu___ -> FStar_Set.empty ()
    | FStar_Reflection_Data.Tv_Const uu___ -> FStar_Set.empty ()
    | FStar_Reflection_Data.Tv_Unknown -> FStar_Set.empty ()
    | FStar_Reflection_Data.Tv_BVar uu___ -> FStar_Set.empty ()
    | FStar_Reflection_Data.Tv_Var x -> FStar_Set.singleton (bv_index x)
    | FStar_Reflection_Data.Tv_App (e1, (e2, uu___)) ->
        FStar_Set.union (freevars e1) (freevars e2)
    | FStar_Reflection_Data.Tv_Abs (b, body) ->
        FStar_Set.union (freevars_binder b) (freevars body)
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        FStar_Set.union (freevars_binder b) (freevars_comp c)
    | FStar_Reflection_Data.Tv_Refine (bv, f) ->
        FStar_Set.union (freevars_bv bv) (freevars f)
    | FStar_Reflection_Data.Tv_Let (recf, attrs, bv, def, body) ->
        FStar_Set.union
          (FStar_Set.union
             (FStar_Set.union (freevars_terms attrs) (freevars_bv bv))
             (freevars def)) (freevars body)
    | FStar_Reflection_Data.Tv_Match (scr, ret, brs) ->
        FStar_Set.union
          (FStar_Set.union (freevars scr)
             (freevars_opt ret freevars_match_returns))
          (freevars_branches brs)
    | FStar_Reflection_Data.Tv_AscribedT (e1, t, tac, b) ->
        FStar_Set.union (FStar_Set.union (freevars e1) (freevars t))
          (freevars_opt tac freevars)
    | FStar_Reflection_Data.Tv_AscribedC (e1, c, tac, b) ->
        FStar_Set.union (FStar_Set.union (freevars e1) (freevars_comp c))
          (freevars_opt tac freevars)
and freevars_opt :
  'a .
    'a FStar_Pervasives_Native.option ->
      ('a -> FStar_Reflection_Data.var FStar_Set.set) ->
        FStar_Reflection_Data.var FStar_Set.set
  =
  fun o ->
    fun f ->
      match o with
      | FStar_Pervasives_Native.None -> FStar_Set.empty ()
      | FStar_Pervasives_Native.Some x -> f x
and (freevars_comp :
  FStar_Reflection_Types.comp -> FStar_Reflection_Data.var FStar_Set.set) =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total t -> freevars t
    | FStar_Reflection_Data.C_GTotal t -> freevars t
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        FStar_Set.union (FStar_Set.union (freevars pre) (freevars post))
          (freevars pats)
    | FStar_Reflection_Data.C_Eff (us, eff_name, res, args, decrs) ->
        FStar_Set.union (FStar_Set.union (freevars res) (freevars_args args))
          (freevars_terms decrs)
and (freevars_args :
  FStar_Reflection_Data.argv Prims.list ->
    FStar_Reflection_Data.var FStar_Set.set)
  =
  fun ts ->
    match ts with
    | [] -> FStar_Set.empty ()
    | (t, q)::ts1 -> FStar_Set.union (freevars t) (freevars_args ts1)
and (freevars_terms :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Data.var FStar_Set.set)
  =
  fun ts ->
    match ts with
    | [] -> FStar_Set.empty ()
    | t::ts1 -> FStar_Set.union (freevars t) (freevars_terms ts1)
and (freevars_bv :
  FStar_Reflection_Types.bv -> FStar_Reflection_Data.var FStar_Set.set) =
  fun b ->
    let bv = FStar_Reflection_Builtins.inspect_bv b in
    freevars bv.FStar_Reflection_Data.bv_sort
and (freevars_binder :
  FStar_Reflection_Types.binder -> FStar_Reflection_Data.var FStar_Set.set) =
  fun b ->
    let bndr = FStar_Reflection_Builtins.inspect_binder b in
    FStar_Set.union (freevars_bv bndr.FStar_Reflection_Data.binder_bv)
      (freevars_terms bndr.FStar_Reflection_Data.binder_attrs)
and (freevars_pattern :
  FStar_Reflection_Data.pattern -> FStar_Reflection_Data.var FStar_Set.set) =
  fun p ->
    match p with
    | FStar_Reflection_Data.Pat_Constant uu___ -> FStar_Set.empty ()
    | FStar_Reflection_Data.Pat_Cons (fv, us, pats) -> freevars_patterns pats
    | FStar_Reflection_Data.Pat_Var bv -> freevars_bv bv
    | FStar_Reflection_Data.Pat_Wild bv -> freevars_bv bv
    | FStar_Reflection_Data.Pat_Dot_Term topt -> freevars_opt topt freevars
and (freevars_patterns :
  (FStar_Reflection_Data.pattern * Prims.bool) Prims.list ->
    FStar_Reflection_Data.var FStar_Set.set)
  =
  fun ps ->
    match ps with
    | [] -> FStar_Set.empty ()
    | (p, b)::ps1 ->
        FStar_Set.union (freevars_pattern p) (freevars_patterns ps1)
and (freevars_branch :
  FStar_Reflection_Data.branch -> FStar_Reflection_Data.var FStar_Set.set) =
  fun br ->
    let uu___ = br in
    match uu___ with
    | (p, t) -> FStar_Set.union (freevars_pattern p) (freevars t)
and (freevars_branches :
  FStar_Reflection_Data.branch Prims.list ->
    FStar_Reflection_Data.var FStar_Set.set)
  =
  fun brs ->
    match brs with
    | [] -> FStar_Set.empty ()
    | hd::tl -> FStar_Set.union (freevars_branch hd) (freevars_branches tl)
and (freevars_match_returns :
  FStar_Reflection_Types.match_returns_ascription ->
    FStar_Reflection_Data.var FStar_Set.set)
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
type term_ctxt =
  | Ctxt_hole 
  | Ctxt_app_head of term_ctxt * FStar_Reflection_Data.argv 
  | Ctxt_app_arg of FStar_Reflection_Types.term *
  FStar_Reflection_Data.aqualv * term_ctxt 
  | Ctxt_abs_binder of binder_ctxt * FStar_Reflection_Types.term 
  | Ctxt_abs_body of FStar_Reflection_Types.binder * term_ctxt 
  | Ctxt_arrow_binder of binder_ctxt * FStar_Reflection_Types.comp 
  | Ctxt_arrow_comp of FStar_Reflection_Types.binder * comp_ctxt 
  | Ctxt_refine_bv of bv_ctxt * FStar_Reflection_Types.term 
  | Ctxt_refine_ref of FStar_Reflection_Types.bv * term_ctxt 
  | Ctxt_let_bv of Prims.bool * FStar_Reflection_Types.term Prims.list *
  bv_ctxt * FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Ctxt_let_def of Prims.bool * FStar_Reflection_Types.term Prims.list *
  FStar_Reflection_Types.bv * term_ctxt * FStar_Reflection_Types.term 
  | Ctxt_let_body of Prims.bool * FStar_Reflection_Types.term Prims.list *
  FStar_Reflection_Types.bv * FStar_Reflection_Types.term * term_ctxt 
  | Ctxt_match_scrutinee of term_ctxt *
  FStar_Reflection_Types.match_returns_ascription
  FStar_Pervasives_Native.option * FStar_Reflection_Data.branch Prims.list 
and bv_ctxt =
  | Ctxt_bv of Prims.string FStar_Sealed.sealed * Prims.nat * term_ctxt 
and binder_ctxt =
  | Ctxt_binder of bv_ctxt * FStar_Reflection_Data.aqualv *
  FStar_Reflection_Types.term Prims.list 
and comp_ctxt =
  | Ctxt_total of term_ctxt 
  | Ctxt_gtotal of term_ctxt 
let uu___is_Ctxt_hole uu___ =
  match uu___ with | Ctxt_hole _ -> true | _ -> false
let uu___is_Ctxt_app_head uu___ =
  match uu___ with | Ctxt_app_head _ -> true | _ -> false
let uu___is_Ctxt_app_arg uu___ =
  match uu___ with | Ctxt_app_arg _ -> true | _ -> false
let uu___is_Ctxt_abs_binder uu___ =
  match uu___ with | Ctxt_abs_binder _ -> true | _ -> false
let uu___is_Ctxt_abs_body uu___ =
  match uu___ with | Ctxt_abs_body _ -> true | _ -> false
let uu___is_Ctxt_arrow_binder uu___ =
  match uu___ with | Ctxt_arrow_binder _ -> true | _ -> false
let uu___is_Ctxt_arrow_comp uu___ =
  match uu___ with | Ctxt_arrow_comp _ -> true | _ -> false
let uu___is_Ctxt_refine_bv uu___ =
  match uu___ with | Ctxt_refine_bv _ -> true | _ -> false
let uu___is_Ctxt_refine_ref uu___ =
  match uu___ with | Ctxt_refine_ref _ -> true | _ -> false
let uu___is_Ctxt_let_bv uu___ =
  match uu___ with | Ctxt_let_bv _ -> true | _ -> false
let uu___is_Ctxt_let_def uu___ =
  match uu___ with | Ctxt_let_def _ -> true | _ -> false
let uu___is_Ctxt_let_body uu___ =
  match uu___ with | Ctxt_let_body _ -> true | _ -> false
let uu___is_Ctxt_match_scrutinee uu___ =
  match uu___ with | Ctxt_match_scrutinee _ -> true | _ -> false
let uu___is_Ctxt_bv uu___ = match uu___ with | Ctxt_bv _ -> true | _ -> false
let uu___is_Ctxt_binder uu___ =
  match uu___ with | Ctxt_binder _ -> true | _ -> false
let uu___is_Ctxt_total uu___ =
  match uu___ with | Ctxt_total _ -> true | _ -> false
let uu___is_Ctxt_gtotal uu___ =
  match uu___ with | Ctxt_gtotal _ -> true | _ -> false
let rec (apply_term_ctxt :
  term_ctxt -> FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun e ->
    fun t ->
      match e with
      | Ctxt_hole -> t
      | Ctxt_app_head (e1, arg) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_App ((apply_term_ctxt e1 t), arg))
      | Ctxt_app_arg (hd, q, e1) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_App (hd, ((apply_term_ctxt e1 t), q)))
      | Ctxt_abs_binder (b, body) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Abs ((apply_binder_ctxt b t), body))
      | Ctxt_abs_body (b, e1) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Abs (b, (apply_term_ctxt e1 t)))
      | Ctxt_arrow_binder (b, c) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Arrow ((apply_binder_ctxt b t), c))
      | Ctxt_arrow_comp (b, c) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Arrow (b, (apply_comp_ctxt c t)))
      | Ctxt_refine_bv (b, phi) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Refine ((apply_bv_ctxt b t), phi))
      | Ctxt_refine_ref (b, phi) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Refine (b, (apply_term_ctxt phi t)))
      | Ctxt_let_bv (b, attrs, bv, def, body) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Let
               (b, attrs, (apply_bv_ctxt bv t), def, body))
      | Ctxt_let_def (b, attrs, bv, def, body) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Let
               (b, attrs, bv, (apply_term_ctxt def t), body))
      | Ctxt_let_body (b, attrs, bv, def, body) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Let
               (b, attrs, bv, def, (apply_term_ctxt body t)))
      | Ctxt_match_scrutinee (sc, ret, brs) ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Match
               ((apply_term_ctxt sc t), ret, brs))
and (apply_bv_ctxt :
  bv_ctxt -> FStar_Reflection_Types.term -> FStar_Reflection_Types.bv) =
  fun b ->
    fun t ->
      let uu___ = b in
      match uu___ with
      | Ctxt_bv (bv_ppname, bv_index1, ty) ->
          FStar_Reflection_Builtins.pack_bv
            {
              FStar_Reflection_Data.bv_ppname = bv_ppname;
              FStar_Reflection_Data.bv_index = bv_index1;
              FStar_Reflection_Data.bv_sort = (apply_term_ctxt ty t)
            }
and (apply_binder_ctxt :
  binder_ctxt -> FStar_Reflection_Types.term -> FStar_Reflection_Types.binder)
  =
  fun b ->
    fun t ->
      let uu___ = b in
      match uu___ with
      | Ctxt_binder (bv, binder_qual1, binder_attrs) ->
          FStar_Reflection_Builtins.pack_binder
            {
              FStar_Reflection_Data.binder_bv = (apply_bv_ctxt bv t);
              FStar_Reflection_Data.binder_qual = binder_qual1;
              FStar_Reflection_Data.binder_attrs = binder_attrs
            }
and (apply_comp_ctxt :
  comp_ctxt -> FStar_Reflection_Types.term -> FStar_Reflection_Types.comp) =
  fun c ->
    fun t ->
      match c with
      | Ctxt_total e ->
          FStar_Reflection_Builtins.pack_comp
            (FStar_Reflection_Data.C_Total (apply_term_ctxt e t))
      | Ctxt_gtotal e ->
          FStar_Reflection_Builtins.pack_comp
            (FStar_Reflection_Data.C_GTotal (apply_term_ctxt e t))
type ('dummyV0, 'dummyV1) constant_typing =
  | CT_Unit 
  | CT_True 
  | CT_False 
let (uu___is_CT_Unit :
  FStar_Reflection_Data.vconst ->
    FStar_Reflection_Types.term -> (unit, unit) constant_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | CT_Unit -> true | uu___2 -> false
let (uu___is_CT_True :
  FStar_Reflection_Data.vconst ->
    FStar_Reflection_Types.term -> (unit, unit) constant_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | CT_True -> true | uu___2 -> false
let (uu___is_CT_False :
  FStar_Reflection_Data.vconst ->
    FStar_Reflection_Types.term -> (unit, unit) constant_typing -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | CT_False -> true | uu___2 -> false
type ('dummyV0, 'dummyV1) univ_eq =
  | UN_Refl of FStar_Reflection_Types.universe 
  | UN_MaxCongL of FStar_Reflection_Types.universe *
  FStar_Reflection_Types.universe * FStar_Reflection_Types.universe * (
  unit, unit) univ_eq 
  | UN_MaxCongR of FStar_Reflection_Types.universe *
  FStar_Reflection_Types.universe * FStar_Reflection_Types.universe * (
  unit, unit) univ_eq 
  | UN_MaxComm of FStar_Reflection_Types.universe *
  FStar_Reflection_Types.universe 
  | UN_MaxLeq of FStar_Reflection_Types.universe *
  FStar_Reflection_Types.universe * (unit, unit) univ_leq 
and ('dummyV0, 'dummyV1) univ_leq =
  | UNLEQ_Refl of FStar_Reflection_Types.universe 
  | UNLEQ_Succ of FStar_Reflection_Types.universe *
  FStar_Reflection_Types.universe * (unit, unit) univ_leq 
  | UNLEQ_Max of FStar_Reflection_Types.universe *
  FStar_Reflection_Types.universe 
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
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun scrutinee ->
    fun then_ ->
      fun else_ ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Match
             (scrutinee, FStar_Pervasives_Native.None,
               [((FStar_Reflection_Data.Pat_Constant
                    FStar_Reflection_Data.C_True), then_);
               ((FStar_Reflection_Data.Pat_Constant
                   FStar_Reflection_Data.C_False), else_)]))
type ('dummyV0, 'dummyV1, 'dummyV2) typing =
  | T_Token of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.typ * unit 
  | T_Var of FStar_Reflection_Types.env * FStar_Reflection_Types.bv 
  | T_FVar of FStar_Reflection_Types.env * FStar_Reflection_Types.fv 
  | T_UInst of FStar_Reflection_Types.env * FStar_Reflection_Types.fv *
  FStar_Reflection_Types.universe Prims.list 
  | T_Const of FStar_Reflection_Types.env * FStar_Reflection_Data.vconst *
  FStar_Reflection_Types.term * (unit, unit) constant_typing 
  | T_Abs of FStar_Reflection_Types.env * FStar_Reflection_Data.var *
  FStar_Reflection_Types.term * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * FStar_Reflection_Types.universe * pp_name_t *
  FStar_Reflection_Data.aqualv * (unit, unit, unit) typing * (unit, unit,
  unit) typing 
  | T_App of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * FStar_Reflection_Types.binder *
  FStar_Reflection_Types.term * (unit, unit, unit) typing * (unit, unit,
  unit) typing 
  | T_Arrow of FStar_Reflection_Types.env * FStar_Reflection_Data.var *
  FStar_Reflection_Types.term * FStar_Reflection_Types.term *
  FStar_Reflection_Types.universe * FStar_Reflection_Types.universe *
  pp_name_t * FStar_Reflection_Data.aqualv * (unit, unit, unit) typing *
  (unit, unit, unit) typing 
  | T_Refine of FStar_Reflection_Types.env * FStar_Reflection_Data.var *
  FStar_Reflection_Types.term * FStar_Reflection_Types.term *
  FStar_Reflection_Types.universe * FStar_Reflection_Types.universe * (
  unit, unit, unit) typing * (unit, unit, unit) typing 
  | T_PropIrrelevance of FStar_Reflection_Types.env *
  FStar_Reflection_Types.term * FStar_Reflection_Types.term * (unit, 
  unit, unit) typing * (unit, unit, unit) typing 
  | T_Sub of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * FStar_Reflection_Types.term * (unit, 
  unit, unit) typing * (unit, unit, unit) sub_typing 
  | T_If of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * FStar_Reflection_Types.universe *
  FStar_Reflection_Data.var * (unit, unit, unit) typing * (unit, unit, 
  unit) typing * (unit, unit, unit) typing * (unit, unit, unit) typing 
  | T_Match of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * FStar_Reflection_Data.branch Prims.list *
  FStar_Reflection_Types.term * (unit, unit, unit) typing * (unit, unit,
  unit, unit, unit) branches_typing 
and ('dummyV0, 'dummyV1, 'dummyV2) sub_typing =
  | ST_Equiv of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * (unit, unit, unit) equiv 
  | ST_Token of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * unit 
  | ST_UnivEq of FStar_Reflection_Types.env * FStar_Reflection_Types.universe
  * FStar_Reflection_Types.universe * (unit, unit) univ_eq 
and ('dummyV0, 'dummyV1, 'dummyV2) equiv =
  | EQ_Refl of FStar_Reflection_Types.env * FStar_Reflection_Types.term 
  | EQ_Sym of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * (unit, unit, unit) equiv 
  | EQ_Trans of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * FStar_Reflection_Types.term * (unit, 
  unit, unit) equiv * (unit, unit, unit) equiv 
  | EQ_Beta of FStar_Reflection_Types.env * FStar_Reflection_Types.typ *
  FStar_Reflection_Data.aqualv * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term 
  | EQ_Token of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * unit 
  | EQ_Ctxt of FStar_Reflection_Types.env * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term * term_ctxt * (unit, unit, unit) equiv 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3, 'dummyV4) branches_typing
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
let uu___is_ST_Equiv uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | ST_Equiv _ -> true | _ -> false
let uu___is_ST_Token uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | ST_Token _ -> true | _ -> false
let uu___is_ST_UnivEq uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | ST_UnivEq _ -> true | _ -> false
let uu___is_EQ_Refl uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | EQ_Refl _ -> true | _ -> false
let uu___is_EQ_Sym uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | EQ_Sym _ -> true | _ -> false
let uu___is_EQ_Trans uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | EQ_Trans _ -> true | _ -> false
let uu___is_EQ_Beta uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | EQ_Beta _ -> true | _ -> false
let uu___is_EQ_Token uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | EQ_Token _ -> true | _ -> false
let uu___is_EQ_Ctxt uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | EQ_Ctxt _ -> true | _ -> false
type bindings =
  (FStar_Reflection_Data.var * FStar_Reflection_Types.term) Prims.list
let rename_bindings :
  'uuuuu .
    ('uuuuu * FStar_Reflection_Types.term) Prims.list ->
      FStar_Reflection_Data.var ->
        FStar_Reflection_Data.var ->
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
let (subtyping_token_renaming :
  FStar_Reflection_Types.env ->
    bindings ->
      bindings ->
        FStar_Reflection_Data.var ->
          FStar_Reflection_Data.var ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  (unit, unit, unit) FStar_Tactics_Builtins.subtyping_token
                    ->
                    (unit, unit, unit) FStar_Tactics_Builtins.subtyping_token)
  =
  fun g ->
    fun bs0 ->
      fun bs1 ->
        fun x ->
          fun y -> fun t -> fun t0 -> fun t1 -> fun d -> Prims.magic ()
let (subtyping_token_weakening :
  FStar_Reflection_Types.env ->
    bindings ->
      bindings ->
        FStar_Reflection_Data.var ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                (unit, unit, unit) FStar_Tactics_Builtins.subtyping_token ->
                  (unit, unit, unit) FStar_Tactics_Builtins.subtyping_token)
  =
  fun g ->
    fun bs0 ->
      fun bs1 ->
        fun x -> fun t -> fun t0 -> fun t1 -> fun d -> Prims.magic ()
let (simplify_umax :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.universe ->
        (unit, unit, unit) typing -> (unit, unit, unit) typing)
  =
  fun g ->
    fun t ->
      fun u ->
        fun d ->
          let ue = UN_MaxLeq (u, u, (UNLEQ_Refl u)) in
          T_Sub
            (g, t, (tm_type (u_max u u)), (tm_type u), d,
              (ST_UnivEq (g, (u_max u u), u, ue)))
let rec (ln' : FStar_Reflection_Types.term -> Prims.int -> Prims.bool) =
  fun e ->
    fun n ->
      match FStar_Reflection_Builtins.inspect_ln e with
      | FStar_Reflection_Data.Tv_UInst (uu___, uu___1) -> true
      | FStar_Reflection_Data.Tv_FVar uu___ -> true
      | FStar_Reflection_Data.Tv_Type uu___ -> true
      | FStar_Reflection_Data.Tv_Const uu___ -> true
      | FStar_Reflection_Data.Tv_Unknown -> true
      | FStar_Reflection_Data.Tv_Var uu___ -> true
      | FStar_Reflection_Data.Tv_BVar m -> (bv_index m) <= n
      | FStar_Reflection_Data.Tv_App (e1, (e2, uu___)) ->
          (ln' e1 n) && (ln' e2 n)
      | FStar_Reflection_Data.Tv_Abs (b, body) ->
          (ln'_binder b n) && (ln' body (n + Prims.int_one))
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          (ln'_binder b n) && (ln'_comp c (n + Prims.int_one))
      | FStar_Reflection_Data.Tv_Refine (bv, f) ->
          (ln'_bv bv n) && (ln' f (n + Prims.int_one))
      | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) -> false
      | FStar_Reflection_Data.Tv_Let (recf, attrs, bv, def, body) ->
          (((ln'_terms attrs n) && (ln'_bv bv n)) &&
             (if recf then ln' def (n + Prims.int_one) else ln' def n))
            && (ln' body (n + Prims.int_one))
      | FStar_Reflection_Data.Tv_Match (scr, ret, brs) ->
          ((ln' scr n) &&
             (match ret with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some m -> ln'_match_returns m n))
            && (ln'_branches brs n)
      | FStar_Reflection_Data.Tv_AscribedT (e1, t, tac, b) ->
          ((ln' e1 n) && (ln' t n)) &&
            ((match tac with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some tac1 -> ln' tac1 n))
      | FStar_Reflection_Data.Tv_AscribedC (e1, c, tac, b) ->
          ((ln' e1 n) && (ln'_comp c n)) &&
            ((match tac with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some tac1 -> ln' tac1 n))
and (ln'_comp : FStar_Reflection_Types.comp -> Prims.int -> Prims.bool) =
  fun c ->
    fun i ->
      match FStar_Reflection_Builtins.inspect_comp c with
      | FStar_Reflection_Data.C_Total t -> ln' t i
      | FStar_Reflection_Data.C_GTotal t -> ln' t i
      | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
          ((ln' pre i) && (ln' post i)) && (ln' pats i)
      | FStar_Reflection_Data.C_Eff (us, eff_name, res, args, decrs) ->
          ((ln' res i) && (ln'_args args i)) && (ln'_terms decrs i)
and (ln'_args :
  FStar_Reflection_Data.argv Prims.list -> Prims.int -> Prims.bool) =
  fun ts ->
    fun i ->
      match ts with
      | [] -> true
      | (t, q)::ts1 -> (ln' t i) && (ln'_args ts1 i)
and (ln'_bv : FStar_Reflection_Types.bv -> Prims.int -> Prims.bool) =
  fun b ->
    fun n ->
      let bv = FStar_Reflection_Builtins.inspect_bv b in
      ln' bv.FStar_Reflection_Data.bv_sort n
and (ln'_binder : FStar_Reflection_Types.binder -> Prims.int -> Prims.bool) =
  fun b ->
    fun n ->
      let bndr = FStar_Reflection_Builtins.inspect_binder b in
      (ln'_bv bndr.FStar_Reflection_Data.binder_bv n) &&
        (ln'_terms bndr.FStar_Reflection_Data.binder_attrs n)
and (ln'_terms :
  FStar_Reflection_Types.term Prims.list -> Prims.int -> Prims.bool) =
  fun ts ->
    fun n ->
      match ts with | [] -> true | t::ts1 -> (ln' t n) && (ln'_terms ts1 n)
and (ln'_patterns :
  (FStar_Reflection_Data.pattern * Prims.bool) Prims.list ->
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
and (ln'_pattern : FStar_Reflection_Data.pattern -> Prims.int -> Prims.bool)
  =
  fun p ->
    fun i ->
      match p with
      | FStar_Reflection_Data.Pat_Constant uu___ -> true
      | FStar_Reflection_Data.Pat_Cons (fv, us, pats) -> ln'_patterns pats i
      | FStar_Reflection_Data.Pat_Var bv -> ln'_bv bv i
      | FStar_Reflection_Data.Pat_Wild bv -> ln'_bv bv i
      | FStar_Reflection_Data.Pat_Dot_Term topt ->
          (match topt with
           | FStar_Pervasives_Native.None -> true
           | FStar_Pervasives_Native.Some t -> ln' t i)
and (ln'_branch : FStar_Reflection_Data.branch -> Prims.int -> Prims.bool) =
  fun br ->
    fun i ->
      let uu___ = br in
      match uu___ with
      | (p, t) ->
          let b = ln'_pattern p i in
          let j = binder_offset_pattern p in
          let b' = ln' t (i + j) in b && b'
and (ln'_branches :
  FStar_Reflection_Data.branch Prims.list -> Prims.int -> Prims.bool) =
  fun brs ->
    fun i ->
      match brs with
      | [] -> true
      | br::brs1 -> (ln'_branch br i) && (ln'_branches brs1 i)
and (ln'_match_returns :
  FStar_Reflection_Types.match_returns_ascription -> Prims.int -> Prims.bool)
  =
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
let (ln : FStar_Reflection_Types.term -> Prims.bool) =
  fun t -> ln' t (Prims.of_int (-1))
let (ln_comp : FStar_Reflection_Types.comp -> Prims.bool) =
  fun c -> ln'_comp c (Prims.of_int (-1))
let (equiv_abs :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.typ ->
          FStar_Reflection_Data.aqualv ->
            FStar_Reflection_Data.var ->
              (unit, unit, unit) equiv -> (unit, unit, unit) equiv)
  =
  fun g ->
    fun e1 ->
      fun e2 ->
        fun uu___ -> fun uu___1 -> fun uu___2 -> fun uu___3 -> Prims.admit ()
type 'g fstar_env_fvs = unit
type fstar_env = FStar_Reflection_Types.env
type fstar_top_env = fstar_env
type dsl_tac_t =
  fstar_top_env ->
    ((FStar_Reflection_Types.term * FStar_Reflection_Types.typ), unit)
      FStar_Tactics_Effect.tac_repr