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
    match t.Pulse_Syntax.term1 with
    | Pulse_Syntax.Tm_Return
        { Pulse_Syntax.ctag = uu___; Pulse_Syntax.insert_eq = uu___1;
          Pulse_Syntax.term = term;_}
        -> freevars term
    | Pulse_Syntax.Tm_Abs
        { Pulse_Syntax.b = b; Pulse_Syntax.q = uu___;
          Pulse_Syntax.pre1 = pre; Pulse_Syntax.body = body;
          Pulse_Syntax.post1 = post;_}
        ->
        FStar_Set.union (freevars b.Pulse_Syntax.binder_ty)
          (FStar_Set.union (freevars_st body)
             (FStar_Set.union (freevars_opt pre) (freevars_opt post)))
    | Pulse_Syntax.Tm_STApp
        { Pulse_Syntax.head = head; Pulse_Syntax.arg_qual = uu___;
          Pulse_Syntax.arg = arg;_}
        -> FStar_Set.union (freevars head) (freevars arg)
    | Pulse_Syntax.Tm_Bind
        { Pulse_Syntax.binder = binder; Pulse_Syntax.head1 = head;
          Pulse_Syntax.body1 = body;_}
        ->
        FStar_Set.union
          (FStar_Set.union (freevars binder.Pulse_Syntax.binder_ty)
             (freevars_st head)) (freevars_st body)
    | Pulse_Syntax.Tm_TotBind
        { Pulse_Syntax.head2 = head; Pulse_Syntax.body2 = body;_} ->
        FStar_Set.union (freevars head) (freevars_st body)
    | Pulse_Syntax.Tm_If
        { Pulse_Syntax.b1 = b; Pulse_Syntax.then_ = then_;
          Pulse_Syntax.else_ = else_; Pulse_Syntax.post2 = post;_}
        ->
        FStar_Set.union (FStar_Set.union (freevars b) (freevars_st then_))
          (FStar_Set.union (freevars_st else_) (freevars_opt post))
    | Pulse_Syntax.Tm_ElimExists { Pulse_Syntax.p = p;_} -> freevars p
    | Pulse_Syntax.Tm_IntroExists
        { Pulse_Syntax.erased = uu___; Pulse_Syntax.p1 = p;
          Pulse_Syntax.witnesses = witnesses;_}
        -> FStar_Set.union (freevars p) (freevars_list witnesses)
    | Pulse_Syntax.Tm_While
        { Pulse_Syntax.invariant = invariant;
          Pulse_Syntax.condition = condition; Pulse_Syntax.body3 = body;_}
        ->
        FStar_Set.union (freevars invariant)
          (FStar_Set.union (freevars_st condition) (freevars_st body))
    | Pulse_Syntax.Tm_Par
        { Pulse_Syntax.pre11 = pre1; Pulse_Syntax.body11 = body1;
          Pulse_Syntax.post11 = post1; Pulse_Syntax.pre2 = pre2;
          Pulse_Syntax.body21 = body2; Pulse_Syntax.post21 = post2;_}
        ->
        FStar_Set.union
          (FStar_Set.union (freevars pre1)
             (FStar_Set.union (freevars_st body1) (freevars post1)))
          (FStar_Set.union (freevars pre2)
             (FStar_Set.union (freevars_st body2) (freevars post2)))
    | Pulse_Syntax.Tm_WithLocal
        { Pulse_Syntax.initializer1 = initializer1;
          Pulse_Syntax.body4 = body;_}
        -> FStar_Set.union (freevars initializer1) (freevars_st body)
    | Pulse_Syntax.Tm_Rewrite { Pulse_Syntax.t1 = t1; Pulse_Syntax.t2 = t2;_}
        -> FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax.Tm_Admit
        { Pulse_Syntax.ctag1 = uu___; Pulse_Syntax.u1 = uu___1;
          Pulse_Syntax.typ = typ; Pulse_Syntax.post3 = post;_}
        -> FStar_Set.union (freevars typ) (freevars_opt post)
    | Pulse_Syntax.Tm_Protect { Pulse_Syntax.t = t1;_} -> freevars_st t1
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
      match t.Pulse_Syntax.term1 with
      | Pulse_Syntax.Tm_Return
          { Pulse_Syntax.ctag = uu___; Pulse_Syntax.insert_eq = uu___1;
            Pulse_Syntax.term = term;_}
          -> ln' term i
      | Pulse_Syntax.Tm_Abs
          { Pulse_Syntax.b = b; Pulse_Syntax.q = uu___;
            Pulse_Syntax.pre1 = pre; Pulse_Syntax.body = body;
            Pulse_Syntax.post1 = post;_}
          ->
          (((ln' b.Pulse_Syntax.binder_ty i) &&
              (ln_st' body (i + Prims.int_one)))
             && (ln_opt' pre (i + Prims.int_one)))
            && (ln_opt' post (i + (Prims.of_int (2))))
      | Pulse_Syntax.Tm_STApp
          { Pulse_Syntax.head = head; Pulse_Syntax.arg_qual = uu___;
            Pulse_Syntax.arg = arg;_}
          -> (ln' head i) && (ln' arg i)
      | Pulse_Syntax.Tm_Bind
          { Pulse_Syntax.binder = binder; Pulse_Syntax.head1 = head;
            Pulse_Syntax.body1 = body;_}
          ->
          ((ln' binder.Pulse_Syntax.binder_ty i) && (ln_st' head i)) &&
            (ln_st' body (i + Prims.int_one))
      | Pulse_Syntax.Tm_TotBind
          { Pulse_Syntax.head2 = head; Pulse_Syntax.body2 = body;_} ->
          (ln' head i) && (ln_st' body (i + Prims.int_one))
      | Pulse_Syntax.Tm_If
          { Pulse_Syntax.b1 = b; Pulse_Syntax.then_ = then_;
            Pulse_Syntax.else_ = else_; Pulse_Syntax.post2 = post;_}
          ->
          (((ln' b i) && (ln_st' then_ i)) && (ln_st' else_ i)) &&
            (ln_opt' post (i + Prims.int_one))
      | Pulse_Syntax.Tm_ElimExists { Pulse_Syntax.p = p;_} -> ln' p i
      | Pulse_Syntax.Tm_IntroExists
          { Pulse_Syntax.erased = uu___; Pulse_Syntax.p1 = p;
            Pulse_Syntax.witnesses = witnesses;_}
          -> (ln' p i) && (ln_list' witnesses i)
      | Pulse_Syntax.Tm_While
          { Pulse_Syntax.invariant = invariant;
            Pulse_Syntax.condition = condition; Pulse_Syntax.body3 = body;_}
          ->
          ((ln' invariant (i + Prims.int_one)) && (ln_st' condition i)) &&
            (ln_st' body i)
      | Pulse_Syntax.Tm_Par
          { Pulse_Syntax.pre11 = pre1; Pulse_Syntax.body11 = body1;
            Pulse_Syntax.post11 = post1; Pulse_Syntax.pre2 = pre2;
            Pulse_Syntax.body21 = body2; Pulse_Syntax.post21 = post2;_}
          ->
          (((((ln' pre1 i) && (ln_st' body1 i)) &&
               (ln' post1 (i + Prims.int_one)))
              && (ln' pre2 i))
             && (ln_st' body2 i))
            && (ln' post2 (i + Prims.int_one))
      | Pulse_Syntax.Tm_WithLocal
          { Pulse_Syntax.initializer1 = initializer1;
            Pulse_Syntax.body4 = body;_}
          -> (ln' initializer1 i) && (ln_st' body (i + Prims.int_one))
      | Pulse_Syntax.Tm_Rewrite
          { Pulse_Syntax.t1 = t1; Pulse_Syntax.t2 = t2;_} ->
          (ln' t1 i) && (ln' t2 i)
      | Pulse_Syntax.Tm_Admit
          { Pulse_Syntax.ctag1 = uu___; Pulse_Syntax.u1 = uu___1;
            Pulse_Syntax.typ = typ; Pulse_Syntax.post3 = post;_}
          -> (ln' typ i) && (ln_opt' post (i + Prims.int_one))
      | Pulse_Syntax.Tm_Protect { Pulse_Syntax.t = t1;_} -> ln_st' t1 i
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
let (open_binder :
  Pulse_Syntax.binder ->
    Pulse_Syntax.term -> Pulse_Syntax.index -> Pulse_Syntax.binder)
  =
  fun b ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax.binder_ty = (open_term' b.Pulse_Syntax.binder_ty v i);
          Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
        }
let rec (open_st_term' :
  Pulse_Syntax.st_term ->
    Pulse_Syntax.term -> Pulse_Syntax.index -> Pulse_Syntax.st_term)
  =
  fun t ->
    fun v ->
      fun i ->
        let t' =
          match t.Pulse_Syntax.term1 with
          | Pulse_Syntax.Tm_Return
              { Pulse_Syntax.ctag = ctag; Pulse_Syntax.insert_eq = insert_eq;
                Pulse_Syntax.term = term;_}
              ->
              Pulse_Syntax.Tm_Return
                {
                  Pulse_Syntax.ctag = ctag;
                  Pulse_Syntax.insert_eq = insert_eq;
                  Pulse_Syntax.term = (open_term' term v i)
                }
          | Pulse_Syntax.Tm_Abs
              { Pulse_Syntax.b = b; Pulse_Syntax.q = q;
                Pulse_Syntax.pre1 = pre; Pulse_Syntax.body = body;
                Pulse_Syntax.post1 = post;_}
              ->
              Pulse_Syntax.Tm_Abs
                {
                  Pulse_Syntax.b = (open_binder b v i);
                  Pulse_Syntax.q = q;
                  Pulse_Syntax.pre1 =
                    (open_term_opt' pre v (i + Prims.int_one));
                  Pulse_Syntax.body =
                    (open_st_term' body v (i + Prims.int_one));
                  Pulse_Syntax.post1 =
                    (open_term_opt' post v (i + (Prims.of_int (2))))
                }
          | Pulse_Syntax.Tm_STApp
              { Pulse_Syntax.head = head; Pulse_Syntax.arg_qual = arg_qual;
                Pulse_Syntax.arg = arg;_}
              ->
              Pulse_Syntax.Tm_STApp
                {
                  Pulse_Syntax.head = (open_term' head v i);
                  Pulse_Syntax.arg_qual = arg_qual;
                  Pulse_Syntax.arg = (open_term' arg v i)
                }
          | Pulse_Syntax.Tm_Bind
              { Pulse_Syntax.binder = binder; Pulse_Syntax.head1 = head;
                Pulse_Syntax.body1 = body;_}
              ->
              Pulse_Syntax.Tm_Bind
                {
                  Pulse_Syntax.binder = (open_binder binder v i);
                  Pulse_Syntax.head1 = (open_st_term' head v i);
                  Pulse_Syntax.body1 =
                    (open_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_TotBind
              { Pulse_Syntax.head2 = head; Pulse_Syntax.body2 = body;_} ->
              Pulse_Syntax.Tm_TotBind
                {
                  Pulse_Syntax.head2 = (open_term' head v i);
                  Pulse_Syntax.body2 =
                    (open_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_If
              { Pulse_Syntax.b1 = b; Pulse_Syntax.then_ = then_;
                Pulse_Syntax.else_ = else_; Pulse_Syntax.post2 = post;_}
              ->
              Pulse_Syntax.Tm_If
                {
                  Pulse_Syntax.b1 = (open_term' b v i);
                  Pulse_Syntax.then_ = (open_st_term' then_ v i);
                  Pulse_Syntax.else_ = (open_st_term' else_ v i);
                  Pulse_Syntax.post2 =
                    (open_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_ElimExists { Pulse_Syntax.p = p;_} ->
              Pulse_Syntax.Tm_ElimExists
                { Pulse_Syntax.p = (open_term' p v i) }
          | Pulse_Syntax.Tm_IntroExists
              { Pulse_Syntax.erased = erased; Pulse_Syntax.p1 = p;
                Pulse_Syntax.witnesses = witnesses;_}
              ->
              Pulse_Syntax.Tm_IntroExists
                {
                  Pulse_Syntax.erased = erased;
                  Pulse_Syntax.p1 = (open_term' p v i);
                  Pulse_Syntax.witnesses = (open_term_list' witnesses v i)
                }
          | Pulse_Syntax.Tm_While
              { Pulse_Syntax.invariant = invariant;
                Pulse_Syntax.condition = condition;
                Pulse_Syntax.body3 = body;_}
              ->
              Pulse_Syntax.Tm_While
                {
                  Pulse_Syntax.invariant =
                    (open_term' invariant v (i + Prims.int_one));
                  Pulse_Syntax.condition = (open_st_term' condition v i);
                  Pulse_Syntax.body3 = (open_st_term' body v i)
                }
          | Pulse_Syntax.Tm_Par
              { Pulse_Syntax.pre11 = pre1; Pulse_Syntax.body11 = body1;
                Pulse_Syntax.post11 = post1; Pulse_Syntax.pre2 = pre2;
                Pulse_Syntax.body21 = body2; Pulse_Syntax.post21 = post2;_}
              ->
              Pulse_Syntax.Tm_Par
                {
                  Pulse_Syntax.pre11 = (open_term' pre1 v i);
                  Pulse_Syntax.body11 = (open_st_term' body1 v i);
                  Pulse_Syntax.post11 =
                    (open_term' post1 v (i + Prims.int_one));
                  Pulse_Syntax.pre2 = (open_term' pre2 v i);
                  Pulse_Syntax.body21 = (open_st_term' body2 v i);
                  Pulse_Syntax.post21 =
                    (open_term' post2 v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_WithLocal
              { Pulse_Syntax.initializer1 = initializer1;
                Pulse_Syntax.body4 = body;_}
              ->
              Pulse_Syntax.Tm_WithLocal
                {
                  Pulse_Syntax.initializer1 = (open_term' initializer1 v i);
                  Pulse_Syntax.body4 =
                    (open_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_Rewrite
              { Pulse_Syntax.t1 = t1; Pulse_Syntax.t2 = t2;_} ->
              Pulse_Syntax.Tm_Rewrite
                {
                  Pulse_Syntax.t1 = (open_term' t1 v i);
                  Pulse_Syntax.t2 = (open_term' t2 v i)
                }
          | Pulse_Syntax.Tm_Admit
              { Pulse_Syntax.ctag1 = ctag; Pulse_Syntax.u1 = u;
                Pulse_Syntax.typ = typ; Pulse_Syntax.post3 = post;_}
              ->
              Pulse_Syntax.Tm_Admit
                {
                  Pulse_Syntax.ctag1 = ctag;
                  Pulse_Syntax.u1 = u;
                  Pulse_Syntax.typ = (open_term' typ v i);
                  Pulse_Syntax.post3 =
                    (open_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_Protect { Pulse_Syntax.t = t1;_} ->
              Pulse_Syntax.Tm_Protect
                { Pulse_Syntax.t = (open_st_term' t1 v i) } in
        {
          Pulse_Syntax.term1 = t';
          Pulse_Syntax.range = (t.Pulse_Syntax.range)
        }
let (open_term_nv :
  Pulse_Syntax.term -> Pulse_Syntax.nvar -> Pulse_Syntax.term) =
  fun t ->
    fun nv -> open_term' t (Pulse_Syntax.term_of_nvar nv) Prims.int_zero
let (open_st_term_nv :
  Pulse_Syntax.st_term -> Pulse_Syntax.nvar -> Pulse_Syntax.st_term) =
  fun t ->
    fun nv -> open_st_term' t (Pulse_Syntax.term_of_nvar nv) Prims.int_zero
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
let (close_binder :
  Pulse_Syntax.binder ->
    Pulse_Syntax.var -> Pulse_Syntax.index -> Pulse_Syntax.binder)
  =
  fun b ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax.binder_ty = (close_term' b.Pulse_Syntax.binder_ty v i);
          Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
        }
let rec (close_st_term' :
  Pulse_Syntax.st_term ->
    Pulse_Syntax.var -> Pulse_Syntax.index -> Pulse_Syntax.st_term)
  =
  fun t ->
    fun v ->
      fun i ->
        let t' =
          match t.Pulse_Syntax.term1 with
          | Pulse_Syntax.Tm_Return
              { Pulse_Syntax.ctag = ctag; Pulse_Syntax.insert_eq = insert_eq;
                Pulse_Syntax.term = term;_}
              ->
              Pulse_Syntax.Tm_Return
                {
                  Pulse_Syntax.ctag = ctag;
                  Pulse_Syntax.insert_eq = insert_eq;
                  Pulse_Syntax.term = (close_term' term v i)
                }
          | Pulse_Syntax.Tm_Abs
              { Pulse_Syntax.b = b; Pulse_Syntax.q = q;
                Pulse_Syntax.pre1 = pre; Pulse_Syntax.body = body;
                Pulse_Syntax.post1 = post;_}
              ->
              Pulse_Syntax.Tm_Abs
                {
                  Pulse_Syntax.b = (close_binder b v i);
                  Pulse_Syntax.q = q;
                  Pulse_Syntax.pre1 =
                    (close_term_opt' pre v (i + Prims.int_one));
                  Pulse_Syntax.body =
                    (close_st_term' body v (i + Prims.int_one));
                  Pulse_Syntax.post1 =
                    (close_term_opt' post v (i + (Prims.of_int (2))))
                }
          | Pulse_Syntax.Tm_STApp
              { Pulse_Syntax.head = head; Pulse_Syntax.arg_qual = arg_qual;
                Pulse_Syntax.arg = arg;_}
              ->
              Pulse_Syntax.Tm_STApp
                {
                  Pulse_Syntax.head = (close_term' head v i);
                  Pulse_Syntax.arg_qual = arg_qual;
                  Pulse_Syntax.arg = (close_term' arg v i)
                }
          | Pulse_Syntax.Tm_Bind
              { Pulse_Syntax.binder = binder; Pulse_Syntax.head1 = head;
                Pulse_Syntax.body1 = body;_}
              ->
              Pulse_Syntax.Tm_Bind
                {
                  Pulse_Syntax.binder = (close_binder binder v i);
                  Pulse_Syntax.head1 = (close_st_term' head v i);
                  Pulse_Syntax.body1 =
                    (close_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_TotBind
              { Pulse_Syntax.head2 = head; Pulse_Syntax.body2 = body;_} ->
              Pulse_Syntax.Tm_TotBind
                {
                  Pulse_Syntax.head2 = (close_term' head v i);
                  Pulse_Syntax.body2 =
                    (close_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_If
              { Pulse_Syntax.b1 = b; Pulse_Syntax.then_ = then_;
                Pulse_Syntax.else_ = else_; Pulse_Syntax.post2 = post;_}
              ->
              Pulse_Syntax.Tm_If
                {
                  Pulse_Syntax.b1 = (close_term' b v i);
                  Pulse_Syntax.then_ = (close_st_term' then_ v i);
                  Pulse_Syntax.else_ = (close_st_term' else_ v i);
                  Pulse_Syntax.post2 =
                    (close_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_ElimExists { Pulse_Syntax.p = p;_} ->
              Pulse_Syntax.Tm_ElimExists
                { Pulse_Syntax.p = (close_term' p v i) }
          | Pulse_Syntax.Tm_IntroExists
              { Pulse_Syntax.erased = erased; Pulse_Syntax.p1 = p;
                Pulse_Syntax.witnesses = witnesses;_}
              ->
              Pulse_Syntax.Tm_IntroExists
                {
                  Pulse_Syntax.erased = erased;
                  Pulse_Syntax.p1 = (close_term' p v i);
                  Pulse_Syntax.witnesses = (close_term_list' witnesses v i)
                }
          | Pulse_Syntax.Tm_While
              { Pulse_Syntax.invariant = invariant;
                Pulse_Syntax.condition = condition;
                Pulse_Syntax.body3 = body;_}
              ->
              Pulse_Syntax.Tm_While
                {
                  Pulse_Syntax.invariant =
                    (close_term' invariant v (i + Prims.int_one));
                  Pulse_Syntax.condition = (close_st_term' condition v i);
                  Pulse_Syntax.body3 = (close_st_term' body v i)
                }
          | Pulse_Syntax.Tm_Par
              { Pulse_Syntax.pre11 = pre1; Pulse_Syntax.body11 = body1;
                Pulse_Syntax.post11 = post1; Pulse_Syntax.pre2 = pre2;
                Pulse_Syntax.body21 = body2; Pulse_Syntax.post21 = post2;_}
              ->
              Pulse_Syntax.Tm_Par
                {
                  Pulse_Syntax.pre11 = (close_term' pre1 v i);
                  Pulse_Syntax.body11 = (close_st_term' body1 v i);
                  Pulse_Syntax.post11 =
                    (close_term' post1 v (i + Prims.int_one));
                  Pulse_Syntax.pre2 = (close_term' pre2 v i);
                  Pulse_Syntax.body21 = (close_st_term' body2 v i);
                  Pulse_Syntax.post21 =
                    (close_term' post2 v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_WithLocal
              { Pulse_Syntax.initializer1 = initializer1;
                Pulse_Syntax.body4 = body;_}
              ->
              Pulse_Syntax.Tm_WithLocal
                {
                  Pulse_Syntax.initializer1 = (close_term' initializer1 v i);
                  Pulse_Syntax.body4 =
                    (close_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_Rewrite
              { Pulse_Syntax.t1 = t1; Pulse_Syntax.t2 = t2;_} ->
              Pulse_Syntax.Tm_Rewrite
                {
                  Pulse_Syntax.t1 = (close_term' t1 v i);
                  Pulse_Syntax.t2 = (close_term' t2 v i)
                }
          | Pulse_Syntax.Tm_Admit
              { Pulse_Syntax.ctag1 = ctag; Pulse_Syntax.u1 = u;
                Pulse_Syntax.typ = typ; Pulse_Syntax.post3 = post;_}
              ->
              Pulse_Syntax.Tm_Admit
                {
                  Pulse_Syntax.ctag1 = ctag;
                  Pulse_Syntax.u1 = u;
                  Pulse_Syntax.typ = (close_term' typ v i);
                  Pulse_Syntax.post3 =
                    (close_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax.Tm_Protect { Pulse_Syntax.t = t1;_} ->
              Pulse_Syntax.Tm_Protect
                { Pulse_Syntax.t = (close_st_term' t1 v i) } in
        {
          Pulse_Syntax.term1 = t';
          Pulse_Syntax.range = (t.Pulse_Syntax.range)
        }
let (close_term : Pulse_Syntax.term -> Pulse_Syntax.var -> Pulse_Syntax.term)
  = fun t -> fun v -> close_term' t v Prims.int_zero
let (close_st_term :
  Pulse_Syntax.st_term -> Pulse_Syntax.var -> Pulse_Syntax.st_term) =
  fun t -> fun v -> close_st_term' t v Prims.int_zero
let (close_comp : Pulse_Syntax.comp -> Pulse_Syntax.var -> Pulse_Syntax.comp)
  = fun t -> fun v -> close_comp' t v Prims.int_zero