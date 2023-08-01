open Prims
let rec (inspect_ln_unascribe :
  FStar_Reflection_Types.term -> FStar_Reflection_V2_Data.term_view) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_AscribedT (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | FStar_Reflection_V2_Data.Tv_AscribedC (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | tv -> tv
let (compare_bv :
  FStar_Reflection_Types.bv -> FStar_Reflection_Types.bv -> FStar_Order.order)
  =
  fun v1 ->
    fun v2 ->
      FStar_Order.compare_int
        (FStar_Reflection_V2_Builtins.inspect_bv v1).FStar_Reflection_V2_Data.index
        (FStar_Reflection_V2_Builtins.inspect_bv v2).FStar_Reflection_V2_Data.index
let (compare_namedv :
  FStar_Reflection_Types.namedv ->
    FStar_Reflection_Types.namedv -> FStar_Order.order)
  =
  fun v1 ->
    fun v2 ->
      FStar_Order.compare_int
        (FStar_Reflection_V2_Builtins.inspect_namedv v1).FStar_Reflection_V2_Data.uniq
        (FStar_Reflection_V2_Builtins.inspect_namedv v2).FStar_Reflection_V2_Data.uniq
let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n ->
    fun s ->
      match s with
      | FStar_Syntax_Syntax.DB (i, t) -> FStar_Syntax_Syntax.DB ((i + n), t)
      | FStar_Syntax_Syntax.DT (i, t) -> FStar_Syntax_Syntax.DT ((i + n), t)
      | FStar_Syntax_Syntax.UN (i, t) -> FStar_Syntax_Syntax.UN ((i + n), t)
      | FStar_Syntax_Syntax.NM (x, i) -> FStar_Syntax_Syntax.NM (x, (i + n))
      | FStar_Syntax_Syntax.UD (x, i) -> FStar_Syntax_Syntax.UD (x, (i + n))
      | FStar_Syntax_Syntax.NT (uu___, uu___1) -> s
let (shift_subst :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list)
  = fun n -> fun s -> FStar_List_Tot_Base.map (shift n) s
let (subst1 :
  FStar_Reflection_Types.namedv ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun n ->
    fun t1 ->
      fun t2 ->
        FStar_Reflection_V2_Builtins.subst_term
          [FStar_Syntax_Syntax.NT (n, t1)] t2
let (mk_binder :
  Prims.string ->
    FStar_Reflection_Types.typ -> FStar_Reflection_V2_Data.simple_binder)
  =
  fun nm ->
    fun sort ->
      let bv =
        {
          FStar_Reflection_V2_Data.sort2 = sort;
          FStar_Reflection_V2_Data.qual = FStar_Reflection_V2_Data.Q_Explicit;
          FStar_Reflection_V2_Data.attrs = [];
          FStar_Reflection_V2_Data.ppname2 = (FStar_Sealed.seal nm)
        } in
      FStar_Reflection_V2_Builtins.pack_binder bv
let (mk_implicit_binder :
  Prims.string -> FStar_Reflection_Types.typ -> FStar_Reflection_Types.binder)
  =
  fun nm ->
    fun sort ->
      FStar_Reflection_V2_Builtins.pack_binder
        {
          FStar_Reflection_V2_Data.sort2 = sort;
          FStar_Reflection_V2_Data.qual = FStar_Reflection_V2_Data.Q_Implicit;
          FStar_Reflection_V2_Data.attrs = [];
          FStar_Reflection_V2_Data.ppname2 = (FStar_Sealed.seal nm)
        }
let (push_binding :
  FStar_Reflection_Types.env ->
    FStar_Reflection_V2_Data.binding -> FStar_Reflection_Types.env)
  =
  fun e ->
    fun b ->
      let nv =
        FStar_Reflection_V2_Builtins.pack_namedv
          {
            FStar_Reflection_V2_Data.uniq =
              (b.FStar_Reflection_V2_Data.uniq1);
            FStar_Reflection_V2_Data.sort =
              (FStar_Sealed.seal b.FStar_Reflection_V2_Data.sort3);
            FStar_Reflection_V2_Data.ppname =
              (b.FStar_Reflection_V2_Data.ppname3)
          } in
      FStar_Reflection_V2_Builtins.push_namedv e nv
let (type_of_binder :
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.typ) =
  fun b ->
    (FStar_Reflection_V2_Builtins.inspect_binder b).FStar_Reflection_V2_Data.sort2
let rec (flatten_name : FStar_Reflection_Types.name -> Prims.string) =
  fun ns ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
let rec (collect_app_ln' :
  FStar_Reflection_V2_Data.argv Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.argv
        Prims.list))
  =
  fun args ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStar_Reflection_V2_Data.Tv_App (l, r) ->
          collect_app_ln' (r :: args) l
      | uu___ -> (t, args)
let (collect_app_ln :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.argv Prims.list))
  = collect_app_ln' []
let rec (mk_app :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.argv Prims.list -> FStar_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      match args with
      | [] -> t
      | x::xs ->
          mk_app
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App (t, x))) xs
let (mk_e_app :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      let e t1 = (t1, FStar_Reflection_V2_Data.Q_Explicit) in
      mk_app t (FStar_List_Tot_Base.map e args)
let (u_unk : FStar_Reflection_Types.universe) =
  FStar_Reflection_V2_Builtins.pack_universe FStar_Reflection_V2_Data.Uv_Unk
let rec (mk_tot_arr_ln :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> cod
      | b::bs1 ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_Arrow
               (b,
                 (FStar_Reflection_V2_Builtins.pack_comp
                    (FStar_Reflection_V2_Data.C_Total (mk_tot_arr_ln bs1 cod)))))
let rec (collect_arr' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.comp))
  =
  fun bs ->
    fun c ->
      match FStar_Reflection_V2_Builtins.inspect_comp c with
      | FStar_Reflection_V2_Data.C_Total t ->
          (match inspect_ln_unascribe t with
           | FStar_Reflection_V2_Data.Tv_Arrow (b, c1) ->
               collect_arr' (b :: bs) c1
           | uu___ -> (bs, c))
      | uu___ -> (bs, c)
let (collect_arr_ln_bs :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.comp))
  =
  fun t ->
    let uu___ =
      collect_arr' []
        (FStar_Reflection_V2_Builtins.pack_comp
           (FStar_Reflection_V2_Data.C_Total t)) in
    match uu___ with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let (collect_arr_ln :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.typ Prims.list * FStar_Reflection_Types.comp))
  =
  fun t ->
    let uu___ = collect_arr_ln_bs t in
    match uu___ with
    | (bs, c) -> ((FStar_List_Tot_Base.map type_of_binder bs), c)
let rec (collect_abs' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.term))
  =
  fun bs ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStar_Reflection_V2_Data.Tv_Abs (b, t') -> collect_abs' (b :: bs) t'
      | uu___ -> (bs, t)
let (collect_abs_ln :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.term))
  =
  fun t ->
    let uu___ = collect_abs' [] t in
    match uu___ with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
let (fv_to_string : FStar_Reflection_Types.fv -> Prims.string) =
  fun fv ->
    FStar_Reflection_V2_Builtins.implode_qn
      (FStar_Reflection_V2_Builtins.inspect_fv fv)
let (mk_stringlit : Prims.string -> FStar_Reflection_Types.term) =
  fun s ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Const
         (FStar_Reflection_V2_Data.C_String s))
let (mk_strcat :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      mk_e_app
        (FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_FVar
              (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "strcat"])))
        [t1; t2]
let (mk_cons :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun h ->
    fun t ->
      mk_e_app
        (FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_FVar
              (FStar_Reflection_V2_Builtins.pack_fv
                 FStar_Reflection_Const.cons_qn))) [h; t]
let (mk_cons_t :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun h ->
      fun t ->
        mk_app
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_FVar
                (FStar_Reflection_V2_Builtins.pack_fv
                   FStar_Reflection_Const.cons_qn)))
          [(ty, FStar_Reflection_V2_Data.Q_Implicit);
          (h, FStar_Reflection_V2_Data.Q_Explicit);
          (t, FStar_Reflection_V2_Data.Q_Explicit)]
let rec (mk_list :
  FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term) =
  fun ts ->
    match ts with
    | [] ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.nil_qn))
    | t::ts1 -> mk_cons t (mk_list ts1)
let (mktuple_n :
  FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term) =
  fun ts ->
    match FStar_List_Tot_Base.length ts with
    | uu___ when uu___ = Prims.int_zero ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_Unit)
    | uu___ when uu___ = Prims.int_one ->
        let uu___1 = ts in (match uu___1 with | x::[] -> x)
    | n ->
        let qn =
          match n with
          | uu___ when uu___ = (Prims.of_int (2)) ->
              FStar_Reflection_Const.mktuple2_qn
          | uu___ when uu___ = (Prims.of_int (3)) ->
              FStar_Reflection_Const.mktuple3_qn
          | uu___ when uu___ = (Prims.of_int (4)) ->
              FStar_Reflection_Const.mktuple4_qn
          | uu___ when uu___ = (Prims.of_int (5)) ->
              FStar_Reflection_Const.mktuple5_qn
          | uu___ when uu___ = (Prims.of_int (6)) ->
              FStar_Reflection_Const.mktuple6_qn
          | uu___ when uu___ = (Prims.of_int (7)) ->
              FStar_Reflection_Const.mktuple7_qn
          | uu___ when uu___ = (Prims.of_int (8)) ->
              FStar_Reflection_Const.mktuple8_qn in
        mk_e_app
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_FVar
                (FStar_Reflection_V2_Builtins.pack_fv qn))) ts
let (destruct_tuple :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = collect_app_ln t in
    match uu___ with
    | (head, args) ->
        (match FStar_Reflection_V2_Builtins.inspect_ln head with
         | FStar_Reflection_V2_Data.Tv_FVar fv ->
             if
               FStar_List_Tot_Base.mem
                 (FStar_Reflection_V2_Builtins.inspect_fv fv)
                 [FStar_Reflection_Const.mktuple2_qn;
                 FStar_Reflection_Const.mktuple3_qn;
                 FStar_Reflection_Const.mktuple4_qn;
                 FStar_Reflection_Const.mktuple5_qn;
                 FStar_Reflection_Const.mktuple6_qn;
                 FStar_Reflection_Const.mktuple7_qn;
                 FStar_Reflection_Const.mktuple8_qn]
             then
               FStar_Pervasives_Native.Some
                 (FStar_List_Tot_Base.concatMap
                    (fun uu___1 ->
                       match uu___1 with
                       | (t1, q) ->
                           (match q with
                            | FStar_Reflection_V2_Data.Q_Explicit -> [t1]
                            | uu___2 -> [])) args)
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
let (mkpair :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  = fun t1 -> fun t2 -> mktuple_n [t1; t2]
let rec (head : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_Match (t1, uu___, uu___1) -> head t1
    | FStar_Reflection_V2_Data.Tv_Let (uu___, uu___1, uu___2, t1, uu___3) ->
        head t1
    | FStar_Reflection_V2_Data.Tv_Abs (uu___, t1) -> head t1
    | FStar_Reflection_V2_Data.Tv_Refine (uu___, t1) -> head t1
    | FStar_Reflection_V2_Data.Tv_App (t1, uu___) -> head t1
    | FStar_Reflection_V2_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        head t1
    | FStar_Reflection_V2_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        head t1
    | FStar_Reflection_V2_Data.Tv_Unknown -> t
    | FStar_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> t
    | FStar_Reflection_V2_Data.Tv_Const uu___ -> t
    | FStar_Reflection_V2_Data.Tv_Type uu___ -> t
    | FStar_Reflection_V2_Data.Tv_Var uu___ -> t
    | FStar_Reflection_V2_Data.Tv_BVar uu___ -> t
    | FStar_Reflection_V2_Data.Tv_FVar uu___ -> t
    | FStar_Reflection_V2_Data.Tv_UInst (uu___, uu___1) -> t
    | FStar_Reflection_V2_Data.Tv_Arrow (uu___, uu___1) -> t
    | FStar_Reflection_V2_Data.Tv_Unsupp -> t
let (is_fvar : FStar_Reflection_Types.term -> Prims.string -> Prims.bool) =
  fun t ->
    fun nm ->
      match inspect_ln_unascribe t with
      | FStar_Reflection_V2_Data.Tv_FVar fv ->
          (FStar_Reflection_V2_Builtins.implode_qn
             (FStar_Reflection_V2_Builtins.inspect_fv fv))
            = nm
      | FStar_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
          (FStar_Reflection_V2_Builtins.implode_qn
             (FStar_Reflection_V2_Builtins.inspect_fv fv))
            = nm
      | uu___ -> false
let rec (is_any_fvar :
  FStar_Reflection_Types.term -> Prims.string Prims.list -> Prims.bool) =
  fun t ->
    fun nms ->
      match nms with
      | [] -> false
      | v::vs -> (is_fvar t v) || (is_any_fvar t vs)
let (is_uvar : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln (head t) with
    | FStar_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> true
    | uu___ -> false
let (binder_set_qual :
  FStar_Reflection_V2_Data.aqualv ->
    FStar_Reflection_Types.binder -> FStar_Reflection_Types.binder)
  =
  fun q ->
    fun b ->
      let bview = FStar_Reflection_V2_Builtins.inspect_binder b in
      FStar_Reflection_V2_Builtins.pack_binder
        {
          FStar_Reflection_V2_Data.sort2 =
            (bview.FStar_Reflection_V2_Data.sort2);
          FStar_Reflection_V2_Data.qual = q;
          FStar_Reflection_V2_Data.attrs =
            (bview.FStar_Reflection_V2_Data.attrs);
          FStar_Reflection_V2_Data.ppname2 =
            (bview.FStar_Reflection_V2_Data.ppname2)
        }
let (add_check_with :
  FStar_VConfig.vconfig ->
    FStar_Reflection_Types.sigelt -> FStar_Reflection_Types.sigelt)
  =
  fun vcfg ->
    fun se ->
      let attrs = FStar_Reflection_V2_Builtins.sigelt_attrs se in
      let vcfg_t = FStar_Reflection_V2_Builtins.embed_vconfig vcfg in
      let t =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             ((FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_FVar
                    (FStar_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "VConfig"; "check_with"]))),
               (vcfg_t, FStar_Reflection_V2_Data.Q_Explicit))) in
      FStar_Reflection_V2_Builtins.set_sigelt_attrs (t :: attrs) se
let (un_uinst : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar fv)
    | uu___ -> t
let rec (is_name_imp :
  FStar_Reflection_Types.name -> FStar_Reflection_Types.term -> Prims.bool) =
  fun nm ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStar_Reflection_V2_Data.Tv_FVar fv ->
          if (FStar_Reflection_V2_Builtins.inspect_fv fv) = nm
          then true
          else false
      | FStar_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
          if (FStar_Reflection_V2_Builtins.inspect_fv fv) = nm
          then true
          else false
      | FStar_Reflection_V2_Data.Tv_App
          (l, (uu___, FStar_Reflection_V2_Data.Q_Implicit)) ->
          is_name_imp nm l
      | uu___ -> false
let (unsquash_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match inspect_ln_unascribe t with
    | FStar_Reflection_V2_Data.Tv_App
        (l, (r, FStar_Reflection_V2_Data.Q_Explicit)) ->
        if is_name_imp FStar_Reflection_Const.squash_qn l
        then FStar_Pervasives_Native.Some r
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (maybe_unsquash_term :
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t ->
    match unsquash_term t with
    | FStar_Pervasives_Native.Some t' -> t'
    | FStar_Pervasives_Native.None -> t