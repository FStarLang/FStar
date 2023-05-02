open Prims
let rec (freevars : Pulse_Syntax.term -> Pulse_Syntax.var FStar_Set.set) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_BVar uu___ -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_FVar uu___ -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_UInst (uu___, uu___1) -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_Constant uu___ -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_Emp -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_Type uu___ -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_VProp -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_Inames -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_EmpInames -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_UVar uu___ -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_Unknown -> FStar_Set.empty ()
    | Pulse_Syntax.Tm_Var nm -> FStar_Set.singleton nm.Pulse_Syntax.nm_index
    | Pulse_Syntax.Tm_Refine (b, body) ->
        FStar_Set.union (freevars b.Pulse_Syntax.binder_ty) (freevars body)
    | Pulse_Syntax.Tm_PureApp (t1, uu___, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax.Tm_Star (t1, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax.Tm_ExistsSL (uu___, t1, t2, uu___1) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax.Tm_ForallSL (uu___, t1, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax.Tm_Let (t1, e1, e2) ->
        FStar_Set.union (FStar_Set.union (freevars t1) (freevars e1))
          (freevars e2)
    | Pulse_Syntax.Tm_Pure p -> freevars p
    | Pulse_Syntax.Tm_FStar t1 -> FStar_Reflection_Typing.freevars t1
    | Pulse_Syntax.Tm_Arrow (b, uu___, body) ->
        FStar_Set.union (freevars b.Pulse_Syntax.binder_ty)
          (freevars_comp body)
and (freevars_comp : Pulse_Syntax.comp -> Pulse_Syntax.var FStar_Set.set) =
  fun c ->
    match c with
    | Pulse_Syntax.C_Tot t -> freevars t
    | Pulse_Syntax.C_ST s -> freevars_st_comp s
    | Pulse_Syntax.C_STAtomic (inames, s) ->
        FStar_Set.union (freevars inames) (freevars_st_comp s)
    | Pulse_Syntax.C_STGhost (inames, s) ->
        FStar_Set.union (freevars inames) (freevars_st_comp s)
and (freevars_st_comp :
  Pulse_Syntax.st_comp -> Pulse_Syntax.var FStar_Set.set) =
  fun s ->
    FStar_Set.union
      (FStar_Set.union (freevars s.Pulse_Syntax.res)
         (freevars s.Pulse_Syntax.pre)) (freevars s.Pulse_Syntax.post)
let (freevars_opt :
  Pulse_Syntax.term FStar_Pervasives_Native.option ->
    Pulse_Syntax.var FStar_Set.set)
  =
  fun t ->
    match t with
    | FStar_Pervasives_Native.None -> FStar_Set.empty ()
    | FStar_Pervasives_Native.Some t1 -> freevars t1
let rec (freevars_list :
  Pulse_Syntax.term Prims.list -> Pulse_Syntax.var FStar_Set.set) =
  fun t ->
    match t with
    | [] -> FStar_Set.empty ()
    | hd::tl -> FStar_Set.union (freevars hd) (freevars_list tl)
let rec (freevars_st :
  Pulse_Syntax.st_term -> Pulse_Syntax.var FStar_Set.set) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_Return (uu___, uu___1, t1) -> freevars t1
    | Pulse_Syntax.Tm_Abs (b, uu___, pre_hint, body, post_hint) ->
        FStar_Set.union (freevars b.Pulse_Syntax.binder_ty)
          (FStar_Set.union (freevars_st body)
             (FStar_Set.union (freevars_opt pre_hint)
                (freevars_opt post_hint)))
    | Pulse_Syntax.Tm_STApp (t1, uu___, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax.Tm_Bind (t1, t2) ->
        FStar_Set.union (freevars_st t1) (freevars_st t2)
    | Pulse_Syntax.Tm_If (t1, e1, e2, post) ->
        FStar_Set.union (FStar_Set.union (freevars t1) (freevars_st e1))
          (FStar_Set.union (freevars_st e2) (freevars_opt post))
    | Pulse_Syntax.Tm_ElimExists p -> freevars p
    | Pulse_Syntax.Tm_IntroExists (uu___, e, p) ->
        FStar_Set.union (freevars e) (freevars_list p)
    | Pulse_Syntax.Tm_While (inv, cond, body) ->
        FStar_Set.union (freevars inv)
          (FStar_Set.union (freevars_st cond) (freevars_st body))
    | Pulse_Syntax.Tm_Par (preL, eL, postL, preR, eR, postR) ->
        FStar_Set.union
          (FStar_Set.union (freevars preL)
             (FStar_Set.union (freevars_st eL) (freevars postL)))
          (FStar_Set.union (freevars preR)
             (FStar_Set.union (freevars_st eR) (freevars postR)))
    | Pulse_Syntax.Tm_WithLocal (t1, t2) ->
        FStar_Set.union (freevars t1) (freevars_st t2)
    | Pulse_Syntax.Tm_Rewrite (t1, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax.Tm_Admit (uu___, uu___1, t1, post) ->
        FStar_Set.union (freevars t1) (freevars_opt post)
    | Pulse_Syntax.Tm_Protect t1 -> freevars_st t1
let rec (ln' : Pulse_Syntax.term -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with
      | Pulse_Syntax.Tm_BVar
          { Pulse_Syntax.bv_index = j; Pulse_Syntax.bv_ppname = uu___;
            Pulse_Syntax.bv_range = uu___1;_}
          -> j <= i
      | Pulse_Syntax.Tm_Var uu___ -> true
      | Pulse_Syntax.Tm_FVar uu___ -> true
      | Pulse_Syntax.Tm_UInst (uu___, uu___1) -> true
      | Pulse_Syntax.Tm_Constant uu___ -> true
      | Pulse_Syntax.Tm_Emp -> true
      | Pulse_Syntax.Tm_Type uu___ -> true
      | Pulse_Syntax.Tm_VProp -> true
      | Pulse_Syntax.Tm_Inames -> true
      | Pulse_Syntax.Tm_EmpInames -> true
      | Pulse_Syntax.Tm_UVar uu___ -> true
      | Pulse_Syntax.Tm_Unknown -> true
      | Pulse_Syntax.Tm_Refine (b, phi) ->
          (ln' b.Pulse_Syntax.binder_ty i) && (ln' phi (i + Prims.int_one))
      | Pulse_Syntax.Tm_PureApp (t1, uu___, t2) -> (ln' t1 i) && (ln' t2 i)
      | Pulse_Syntax.Tm_Star (t1, t2) -> (ln' t1 i) && (ln' t2 i)
      | Pulse_Syntax.Tm_Let (t1, e1, e2) ->
          ((ln' t1 i) && (ln' e1 i)) && (ln' e2 (i + Prims.int_one))
      | Pulse_Syntax.Tm_Pure p -> ln' p i
      | Pulse_Syntax.Tm_ExistsSL (uu___, t1, body, uu___1) ->
          (ln' t1 i) && (ln' body (i + Prims.int_one))
      | Pulse_Syntax.Tm_ForallSL (uu___, t1, body) ->
          (ln' t1 i) && (ln' body (i + Prims.int_one))
      | Pulse_Syntax.Tm_Arrow (b, uu___, c) ->
          (ln' b.Pulse_Syntax.binder_ty i) && (ln_c' c (i + Prims.int_one))
      | Pulse_Syntax.Tm_FStar t1 -> FStar_Reflection_Typing.ln' t1 i
and (ln_c' : Pulse_Syntax.comp -> Prims.int -> Prims.bool) =
  fun c ->
    fun i ->
      match c with
      | Pulse_Syntax.C_Tot t -> ln' t i
      | Pulse_Syntax.C_ST s -> ln_st_comp s i
      | Pulse_Syntax.C_STAtomic (inames, s) ->
          (ln' inames i) && (ln_st_comp s i)
      | Pulse_Syntax.C_STGhost (inames, s) ->
          (ln' inames i) && (ln_st_comp s i)
and (ln_st_comp : Pulse_Syntax.st_comp -> Prims.int -> Prims.bool) =
  fun s ->
    fun i ->
      ((ln' s.Pulse_Syntax.res i) && (ln' s.Pulse_Syntax.pre i)) &&
        (ln' s.Pulse_Syntax.post (i + Prims.int_one))
let (ln_opt' :
  Pulse_Syntax.term FStar_Pervasives_Native.option -> Prims.int -> Prims.bool)
  =
  fun t ->
    fun i ->
      match t with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some t1 -> ln' t1 i
let rec (ln_list' : Pulse_Syntax.term Prims.list -> Prims.int -> Prims.bool)
  =
  fun t ->
    fun i ->
      match t with | [] -> true | hd::tl -> (ln' hd i) && (ln_list' tl i)
let rec (ln_st' : Pulse_Syntax.st_term -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with
      | Pulse_Syntax.Tm_Return (uu___, uu___1, t1) -> ln' t1 i
      | Pulse_Syntax.Tm_Abs (b, uu___, pre_hint, body, post) ->
          (((ln' b.Pulse_Syntax.binder_ty i) &&
              (ln_st' body (i + Prims.int_one)))
             && (ln_opt' pre_hint (i + Prims.int_one)))
            && (ln_opt' post (i + (Prims.of_int (2))))
      | Pulse_Syntax.Tm_STApp (t1, uu___, t2) -> (ln' t1 i) && (ln' t2 i)
      | Pulse_Syntax.Tm_Bind (t1, t2) ->
          (ln_st' t1 i) && (ln_st' t2 (i + Prims.int_one))
      | Pulse_Syntax.Tm_If (b, then_, else_, post) ->
          (((ln' b i) && (ln_st' then_ i)) && (ln_st' else_ i)) &&
            (ln_opt' post (i + Prims.int_one))
      | Pulse_Syntax.Tm_ElimExists p -> ln' p i
      | Pulse_Syntax.Tm_IntroExists (uu___, p, e) ->
          (ln' p i) && (ln_list' e i)
      | Pulse_Syntax.Tm_While (inv, cond, body) ->
          ((ln' inv (i + Prims.int_one)) && (ln_st' cond i)) &&
            (ln_st' body i)
      | Pulse_Syntax.Tm_Par (preL, eL, postL, preR, eR, postR) ->
          (((((ln' preL i) && (ln_st' eL i)) &&
               (ln' postL (i + Prims.int_one)))
              && (ln' preR i))
             && (ln_st' eR i))
            && (ln' postR (i + Prims.int_one))
      | Pulse_Syntax.Tm_WithLocal (t1, t2) ->
          (ln' t1 i) && (ln_st' t2 (i + Prims.int_one))
      | Pulse_Syntax.Tm_Rewrite (t1, t2) -> (ln' t1 i) && (ln' t2 i)
      | Pulse_Syntax.Tm_Admit (uu___, uu___1, t1, post) ->
          (ln' t1 i) && (ln_opt' post (i + Prims.int_one))
      | Pulse_Syntax.Tm_Protect t1 -> ln_st' t1 i
let (ln : Pulse_Syntax.term -> Prims.bool) =
  fun t -> ln' t (Prims.of_int (-1))
let (ln_st : Pulse_Syntax.st_term -> Prims.bool) =
  fun t -> ln_st' t (Prims.of_int (-1))
let (ln_c : Pulse_Syntax.comp -> Prims.bool) =
  fun c -> ln_c' c (Prims.of_int (-1))
let rec (open_term' :
  Pulse_Syntax.term ->
    Pulse_Syntax.term -> Pulse_Syntax.index -> Pulse_Syntax.term)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Pulse_Syntax.Tm_BVar bv ->
            if i = bv.Pulse_Syntax.bv_index then v else t
        | Pulse_Syntax.Tm_Var uu___ -> t
        | Pulse_Syntax.Tm_FVar uu___ -> t
        | Pulse_Syntax.Tm_UInst (uu___, uu___1) -> t
        | Pulse_Syntax.Tm_Constant uu___ -> t
        | Pulse_Syntax.Tm_Type uu___ -> t
        | Pulse_Syntax.Tm_VProp -> t
        | Pulse_Syntax.Tm_Emp -> t
        | Pulse_Syntax.Tm_Inames -> t
        | Pulse_Syntax.Tm_EmpInames -> t
        | Pulse_Syntax.Tm_UVar uu___ -> t
        | Pulse_Syntax.Tm_Unknown -> t
        | Pulse_Syntax.Tm_Refine (b, phi) ->
            Pulse_Syntax.Tm_Refine
              ({
                 Pulse_Syntax.binder_ty =
                   (open_term' b.Pulse_Syntax.binder_ty v i);
                 Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
               }, (open_term' phi v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_PureApp (head, q, arg) ->
            Pulse_Syntax.Tm_PureApp
              ((open_term' head v i), q, (open_term' arg v i))
        | Pulse_Syntax.Tm_Let (t1, e1, e2) ->
            Pulse_Syntax.Tm_Let
              ((open_term' t1 v i), (open_term' e1 v i),
                (open_term' e2 v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Pure p -> Pulse_Syntax.Tm_Pure (open_term' p v i)
        | Pulse_Syntax.Tm_Star (l, r) ->
            Pulse_Syntax.Tm_Star ((open_term' l v i), (open_term' r v i))
        | Pulse_Syntax.Tm_ExistsSL (u, t1, body, se) ->
            Pulse_Syntax.Tm_ExistsSL
              (u, (open_term' t1 v i),
                (open_term' body v (i + Prims.int_one)), se)
        | Pulse_Syntax.Tm_ForallSL (u, t1, body) ->
            Pulse_Syntax.Tm_ForallSL
              (u, (open_term' t1 v i),
                (open_term' body v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Arrow (b, q, c) ->
            Pulse_Syntax.Tm_Arrow
              ({
                 Pulse_Syntax.binder_ty =
                   (open_term' b.Pulse_Syntax.binder_ty v i);
                 Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
               }, q, (open_comp' c v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_FStar t1 ->
            Pulse_Syntax.Tm_FStar
              (FStar_Reflection_Typing.open_or_close_term' t1
                 (FStar_Reflection_Typing.OpenWith
                    (Pulse_Elaborate_Pure.elab_term v)) i)
and (open_comp' :
  Pulse_Syntax.comp ->
    Pulse_Syntax.term -> Pulse_Syntax.index -> Pulse_Syntax.comp)
  =
  fun c ->
    fun v ->
      fun i ->
        match c with
        | Pulse_Syntax.C_Tot t -> Pulse_Syntax.C_Tot (open_term' t v i)
        | Pulse_Syntax.C_ST s -> Pulse_Syntax.C_ST (open_st_comp' s v i)
        | Pulse_Syntax.C_STAtomic (inames, s) ->
            Pulse_Syntax.C_STAtomic
              ((open_term' inames v i), (open_st_comp' s v i))
        | Pulse_Syntax.C_STGhost (inames, s) ->
            Pulse_Syntax.C_STGhost
              ((open_term' inames v i), (open_st_comp' s v i))
and (open_st_comp' :
  Pulse_Syntax.st_comp ->
    Pulse_Syntax.term -> Pulse_Syntax.index -> Pulse_Syntax.st_comp)
  =
  fun s ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax.u = (s.Pulse_Syntax.u);
          Pulse_Syntax.res = (open_term' s.Pulse_Syntax.res v i);
          Pulse_Syntax.pre = (open_term' s.Pulse_Syntax.pre v i);
          Pulse_Syntax.post =
            (open_term' s.Pulse_Syntax.post v (i + Prims.int_one))
        }
let (open_term_opt' :
  Pulse_Syntax.term FStar_Pervasives_Native.option ->
    Pulse_Syntax.term ->
      Pulse_Syntax.index -> Pulse_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t1 ->
            FStar_Pervasives_Native.Some (open_term' t1 v i)
let rec (open_term_list' :
  Pulse_Syntax.term Prims.list ->
    Pulse_Syntax.term -> Pulse_Syntax.index -> Pulse_Syntax.term Prims.list)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | [] -> []
        | hd::tl -> (open_term' hd v i) :: (open_term_list' tl v i)
let rec (open_st_term' :
  Pulse_Syntax.st_term ->
    Pulse_Syntax.term -> Pulse_Syntax.index -> Pulse_Syntax.st_term)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Pulse_Syntax.Tm_Return (c, use_eq, t1) ->
            Pulse_Syntax.Tm_Return (c, use_eq, (open_term' t1 v i))
        | Pulse_Syntax.Tm_Abs (b, q, pre_hint, body, post) ->
            Pulse_Syntax.Tm_Abs
              ({
                 Pulse_Syntax.binder_ty =
                   (open_term' b.Pulse_Syntax.binder_ty v i);
                 Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
               }, q, (open_term_opt' pre_hint v (i + Prims.int_one)),
                (open_st_term' body v (i + Prims.int_one)),
                (open_term_opt' post v (i + (Prims.of_int (2)))))
        | Pulse_Syntax.Tm_STApp (head, q, arg) ->
            Pulse_Syntax.Tm_STApp
              ((open_term' head v i), q, (open_term' arg v i))
        | Pulse_Syntax.Tm_Bind (e1, e2) ->
            Pulse_Syntax.Tm_Bind
              ((open_st_term' e1 v i),
                (open_st_term' e2 v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_If (b, then_, else_, post) ->
            Pulse_Syntax.Tm_If
              ((open_term' b v i), (open_st_term' then_ v i),
                (open_st_term' else_ v i),
                (open_term_opt' post v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_ElimExists p ->
            Pulse_Syntax.Tm_ElimExists (open_term' p v i)
        | Pulse_Syntax.Tm_IntroExists (b, p, e) ->
            Pulse_Syntax.Tm_IntroExists
              (b, (open_term' p v i), (open_term_list' e v i))
        | Pulse_Syntax.Tm_While (inv, cond, body) ->
            Pulse_Syntax.Tm_While
              ((open_term' inv v (i + Prims.int_one)),
                (open_st_term' cond v i), (open_st_term' body v i))
        | Pulse_Syntax.Tm_Par (preL, eL, postL, preR, eR, postR) ->
            Pulse_Syntax.Tm_Par
              ((open_term' preL v i), (open_st_term' eL v i),
                (open_term' postL v (i + Prims.int_one)),
                (open_term' preR v i), (open_st_term' eR v i),
                (open_term' postR v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_WithLocal (e1, e2) ->
            Pulse_Syntax.Tm_WithLocal
              ((open_term' e1 v i), (open_st_term' e2 v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Rewrite (e1, e2) ->
            Pulse_Syntax.Tm_Rewrite
              ((open_term' e1 v i), (open_term' e2 v i))
        | Pulse_Syntax.Tm_Admit (c, u, t1, post) ->
            Pulse_Syntax.Tm_Admit
              (c, u, (open_term' t1 v i),
                (open_term_opt' post v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Protect t1 ->
            Pulse_Syntax.Tm_Protect (open_st_term' t1 v i)
let (open_term : Pulse_Syntax.term -> Pulse_Syntax.var -> Pulse_Syntax.term)
  =
  fun t ->
    fun v ->
      open_term' t
        (Pulse_Syntax.Tm_Var
           {
             Pulse_Syntax.nm_index = v;
             Pulse_Syntax.nm_ppname = FStar_Reflection_Typing.pp_name_default;
             Pulse_Syntax.nm_range = FStar_Range.range_0
           }) Prims.int_zero
let (open_st_term :
  Pulse_Syntax.st_term -> Pulse_Syntax.var -> Pulse_Syntax.st_term) =
  fun t ->
    fun v ->
      open_st_term' t
        (Pulse_Syntax.Tm_Var
           {
             Pulse_Syntax.nm_index = v;
             Pulse_Syntax.nm_ppname = FStar_Reflection_Typing.pp_name_default;
             Pulse_Syntax.nm_range = FStar_Range.range_0
           }) Prims.int_zero
let (open_comp_with :
  Pulse_Syntax.comp -> Pulse_Syntax.term -> Pulse_Syntax.comp) =
  fun c -> fun x -> open_comp' c x Prims.int_zero
let rec (close_term' :
  Pulse_Syntax.term ->
    Pulse_Syntax.var -> Pulse_Syntax.index -> Pulse_Syntax.term)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Pulse_Syntax.Tm_Var nm ->
            if nm.Pulse_Syntax.nm_index = v
            then
              Pulse_Syntax.Tm_BVar
                {
                  Pulse_Syntax.bv_index = i;
                  Pulse_Syntax.bv_ppname = (nm.Pulse_Syntax.nm_ppname);
                  Pulse_Syntax.bv_range = (nm.Pulse_Syntax.nm_range)
                }
            else t
        | Pulse_Syntax.Tm_BVar uu___ -> t
        | Pulse_Syntax.Tm_FVar uu___ -> t
        | Pulse_Syntax.Tm_UInst (uu___, uu___1) -> t
        | Pulse_Syntax.Tm_Constant uu___ -> t
        | Pulse_Syntax.Tm_Type uu___ -> t
        | Pulse_Syntax.Tm_VProp -> t
        | Pulse_Syntax.Tm_Emp -> t
        | Pulse_Syntax.Tm_Inames -> t
        | Pulse_Syntax.Tm_EmpInames -> t
        | Pulse_Syntax.Tm_UVar uu___ -> t
        | Pulse_Syntax.Tm_Unknown -> t
        | Pulse_Syntax.Tm_Refine (b, phi) ->
            Pulse_Syntax.Tm_Refine
              ({
                 Pulse_Syntax.binder_ty =
                   (close_term' b.Pulse_Syntax.binder_ty v i);
                 Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
               }, (close_term' phi v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_PureApp (head, q, arg) ->
            Pulse_Syntax.Tm_PureApp
              ((close_term' head v i), q, (close_term' arg v i))
        | Pulse_Syntax.Tm_Let (t1, e1, e2) ->
            Pulse_Syntax.Tm_Let
              ((close_term' t1 v i), (close_term' e1 v i),
                (close_term' e2 v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Pure p -> Pulse_Syntax.Tm_Pure (close_term' p v i)
        | Pulse_Syntax.Tm_Star (l, r) ->
            Pulse_Syntax.Tm_Star ((close_term' l v i), (close_term' r v i))
        | Pulse_Syntax.Tm_ExistsSL (u, t1, body, se) ->
            Pulse_Syntax.Tm_ExistsSL
              (u, (close_term' t1 v i),
                (close_term' body v (i + Prims.int_one)), se)
        | Pulse_Syntax.Tm_ForallSL (u, t1, body) ->
            Pulse_Syntax.Tm_ForallSL
              (u, (close_term' t1 v i),
                (close_term' body v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Arrow (b, q, c) ->
            Pulse_Syntax.Tm_Arrow
              ({
                 Pulse_Syntax.binder_ty =
                   (close_term' b.Pulse_Syntax.binder_ty v i);
                 Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
               }, q, (close_comp' c v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_FStar t1 ->
            Pulse_Syntax.Tm_FStar
              (FStar_Reflection_Typing.open_or_close_term' t1
                 (FStar_Reflection_Typing.CloseVar v) i)
and (close_comp' :
  Pulse_Syntax.comp ->
    Pulse_Syntax.var -> Pulse_Syntax.index -> Pulse_Syntax.comp)
  =
  fun c ->
    fun v ->
      fun i ->
        match c with
        | Pulse_Syntax.C_Tot t -> Pulse_Syntax.C_Tot (close_term' t v i)
        | Pulse_Syntax.C_ST s -> Pulse_Syntax.C_ST (close_st_comp' s v i)
        | Pulse_Syntax.C_STAtomic (inames, s) ->
            Pulse_Syntax.C_STAtomic
              ((close_term' inames v i), (close_st_comp' s v i))
        | Pulse_Syntax.C_STGhost (inames, s) ->
            Pulse_Syntax.C_STGhost
              ((close_term' inames v i), (close_st_comp' s v i))
and (close_st_comp' :
  Pulse_Syntax.st_comp ->
    Pulse_Syntax.var -> Pulse_Syntax.index -> Pulse_Syntax.st_comp)
  =
  fun s ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax.u = (s.Pulse_Syntax.u);
          Pulse_Syntax.res = (close_term' s.Pulse_Syntax.res v i);
          Pulse_Syntax.pre = (close_term' s.Pulse_Syntax.pre v i);
          Pulse_Syntax.post =
            (close_term' s.Pulse_Syntax.post v (i + Prims.int_one))
        }
let (close_term_opt' :
  Pulse_Syntax.term FStar_Pervasives_Native.option ->
    Pulse_Syntax.var ->
      Pulse_Syntax.index -> Pulse_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t1 ->
            FStar_Pervasives_Native.Some (close_term' t1 v i)
let rec (close_term_list' :
  Pulse_Syntax.term Prims.list ->
    Pulse_Syntax.var -> Pulse_Syntax.index -> Pulse_Syntax.term Prims.list)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | [] -> []
        | hd::tl -> (close_term' hd v i) :: (close_term_list' tl v i)
let rec (close_st_term' :
  Pulse_Syntax.st_term ->
    Pulse_Syntax.var -> Pulse_Syntax.index -> Pulse_Syntax.st_term)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Pulse_Syntax.Tm_Return (c, use_eq, t1) ->
            Pulse_Syntax.Tm_Return (c, use_eq, (close_term' t1 v i))
        | Pulse_Syntax.Tm_Abs (b, q, pre_hint, body, post) ->
            Pulse_Syntax.Tm_Abs
              ({
                 Pulse_Syntax.binder_ty =
                   (close_term' b.Pulse_Syntax.binder_ty v i);
                 Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
               }, q, (close_term_opt' pre_hint v (i + Prims.int_one)),
                (close_st_term' body v (i + Prims.int_one)),
                (close_term_opt' post v (i + (Prims.of_int (2)))))
        | Pulse_Syntax.Tm_STApp (head, q, arg) ->
            Pulse_Syntax.Tm_STApp
              ((close_term' head v i), q, (close_term' arg v i))
        | Pulse_Syntax.Tm_Bind (e1, e2) ->
            Pulse_Syntax.Tm_Bind
              ((close_st_term' e1 v i),
                (close_st_term' e2 v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_If (b, then_, else_, post) ->
            Pulse_Syntax.Tm_If
              ((close_term' b v i), (close_st_term' then_ v i),
                (close_st_term' else_ v i),
                (close_term_opt' post v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_ElimExists p ->
            Pulse_Syntax.Tm_ElimExists (close_term' p v i)
        | Pulse_Syntax.Tm_IntroExists (b, p, e) ->
            Pulse_Syntax.Tm_IntroExists
              (b, (close_term' p v i), (close_term_list' e v i))
        | Pulse_Syntax.Tm_While (inv, cond, body) ->
            Pulse_Syntax.Tm_While
              ((close_term' inv v (i + Prims.int_one)),
                (close_st_term' cond v i), (close_st_term' body v i))
        | Pulse_Syntax.Tm_Par (preL, eL, postL, preR, eR, postR) ->
            Pulse_Syntax.Tm_Par
              ((close_term' preL v i), (close_st_term' eL v i),
                (close_term' postL v (i + Prims.int_one)),
                (close_term' preR v i), (close_st_term' eR v i),
                (close_term' postR v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_WithLocal (e1, e2) ->
            Pulse_Syntax.Tm_WithLocal
              ((close_term' e1 v i),
                (close_st_term' e2 v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Rewrite (e1, e2) ->
            Pulse_Syntax.Tm_Rewrite
              ((close_term' e1 v i), (close_term' e2 v i))
        | Pulse_Syntax.Tm_Admit (c, u, t1, post) ->
            Pulse_Syntax.Tm_Admit
              (c, u, (close_term' t1 v i),
                (close_term_opt' post v (i + Prims.int_one)))
        | Pulse_Syntax.Tm_Protect t1 ->
            Pulse_Syntax.Tm_Protect (close_st_term' t1 v i)
let (close_term : Pulse_Syntax.term -> Pulse_Syntax.var -> Pulse_Syntax.term)
  = fun t -> fun v -> close_term' t v Prims.int_zero
let (close_st_term :
  Pulse_Syntax.st_term -> Pulse_Syntax.var -> Pulse_Syntax.st_term) =
  fun t -> fun v -> close_st_term' t v Prims.int_zero
let (close_comp : Pulse_Syntax.comp -> Pulse_Syntax.var -> Pulse_Syntax.comp)
  = fun t -> fun v -> close_comp' t v Prims.int_zero