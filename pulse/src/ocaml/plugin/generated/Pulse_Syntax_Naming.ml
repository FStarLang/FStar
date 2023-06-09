open Prims
let rec (freevars :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_Emp -> FStar_Set.empty ()
    | Pulse_Syntax_Base.Tm_VProp -> FStar_Set.empty ()
    | Pulse_Syntax_Base.Tm_Inames -> FStar_Set.empty ()
    | Pulse_Syntax_Base.Tm_EmpInames -> FStar_Set.empty ()
    | Pulse_Syntax_Base.Tm_Unknown -> FStar_Set.empty ()
    | Pulse_Syntax_Base.Tm_Star (t1, t2) ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax_Base.Tm_ExistsSL (uu___, t1, t2) ->
        FStar_Set.union (freevars t1.Pulse_Syntax_Base.binder_ty)
          (freevars t2)
    | Pulse_Syntax_Base.Tm_ForallSL (uu___, t1, t2) ->
        FStar_Set.union (freevars t1.Pulse_Syntax_Base.binder_ty)
          (freevars t2)
    | Pulse_Syntax_Base.Tm_Pure p -> freevars p
    | Pulse_Syntax_Base.Tm_FStar (t1, uu___) ->
        FStar_Reflection_Typing.freevars t1
let (freevars_st_comp :
  Pulse_Syntax_Base.st_comp -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun s ->
    FStar_Set.union
      (FStar_Set.union (freevars s.Pulse_Syntax_Base.res)
         (freevars s.Pulse_Syntax_Base.pre))
      (freevars s.Pulse_Syntax_Base.post)
let (freevars_comp :
  Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t -> freevars t
    | Pulse_Syntax_Base.C_ST s -> freevars_st_comp s
    | Pulse_Syntax_Base.C_STAtomic (inames, s) ->
        FStar_Set.union (freevars inames) (freevars_st_comp s)
    | Pulse_Syntax_Base.C_STGhost (inames, s) ->
        FStar_Set.union (freevars inames) (freevars_st_comp s)
let (freevars_opt :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    Pulse_Syntax_Base.var FStar_Set.set)
  =
  fun t ->
    match t with
    | FStar_Pervasives_Native.None -> FStar_Set.empty ()
    | FStar_Pervasives_Native.Some t1 -> freevars t1
let rec (freevars_list :
  Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun t ->
    match t with
    | [] -> FStar_Set.empty ()
    | hd::tl -> FStar_Set.union (freevars hd) (freevars_list tl)
let rec (freevars_st :
  Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.ctag = uu___;
          Pulse_Syntax_Base.insert_eq = uu___1;
          Pulse_Syntax_Base.term = term;_}
        -> freevars term
    | Pulse_Syntax_Base.Tm_Abs
        { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = uu___;
          Pulse_Syntax_Base.pre1 = pre; Pulse_Syntax_Base.body = body;
          Pulse_Syntax_Base.ret_ty = ret_ty;
          Pulse_Syntax_Base.post1 = post;_}
        ->
        FStar_Set.union (freevars b.Pulse_Syntax_Base.binder_ty)
          (FStar_Set.union (freevars_st body)
             (FStar_Set.union (freevars_opt pre)
                (FStar_Set.union (freevars_opt ret_ty) (freevars_opt post))))
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = head; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = arg;_}
        -> FStar_Set.union (freevars head) (freevars arg)
    | Pulse_Syntax_Base.Tm_Bind
        { Pulse_Syntax_Base.binder = binder; Pulse_Syntax_Base.head1 = head;
          Pulse_Syntax_Base.body1 = body;_}
        ->
        FStar_Set.union
          (FStar_Set.union (freevars binder.Pulse_Syntax_Base.binder_ty)
             (freevars_st head)) (freevars_st body)
    | Pulse_Syntax_Base.Tm_TotBind
        { Pulse_Syntax_Base.head2 = head; Pulse_Syntax_Base.body2 = body;_}
        -> FStar_Set.union (freevars head) (freevars_st body)
    | Pulse_Syntax_Base.Tm_If
        { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
          Pulse_Syntax_Base.else_ = else_; Pulse_Syntax_Base.post2 = post;_}
        ->
        FStar_Set.union (FStar_Set.union (freevars b) (freevars_st then_))
          (FStar_Set.union (freevars_st else_) (freevars_opt post))
    | Pulse_Syntax_Base.Tm_IntroPure
        { Pulse_Syntax_Base.p = p; Pulse_Syntax_Base.should_check = uu___;_}
        -> freevars p
    | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p1 = p;_} ->
        freevars p
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = uu___; Pulse_Syntax_Base.p2 = p;
          Pulse_Syntax_Base.witnesses = witnesses;
          Pulse_Syntax_Base.should_check1 = uu___1;_}
        -> FStar_Set.union (freevars p) (freevars_list witnesses)
    | Pulse_Syntax_Base.Tm_While
        { Pulse_Syntax_Base.invariant = invariant;
          Pulse_Syntax_Base.condition = condition;
          Pulse_Syntax_Base.condition_var = uu___;
          Pulse_Syntax_Base.body3 = body;_}
        ->
        FStar_Set.union (freevars invariant)
          (FStar_Set.union (freevars_st condition) (freevars_st body))
    | Pulse_Syntax_Base.Tm_Par
        { Pulse_Syntax_Base.pre11 = pre1; Pulse_Syntax_Base.body11 = body1;
          Pulse_Syntax_Base.post11 = post1; Pulse_Syntax_Base.pre2 = pre2;
          Pulse_Syntax_Base.body21 = body2;
          Pulse_Syntax_Base.post21 = post2;_}
        ->
        FStar_Set.union
          (FStar_Set.union (freevars pre1)
             (FStar_Set.union (freevars_st body1) (freevars post1)))
          (FStar_Set.union (freevars pre2)
             (FStar_Set.union (freevars_st body2) (freevars post2)))
    | Pulse_Syntax_Base.Tm_WithLocal
        { Pulse_Syntax_Base.binder1 = binder;
          Pulse_Syntax_Base.initializer1 = initializer1;
          Pulse_Syntax_Base.body4 = body;_}
        ->
        FStar_Set.union (freevars binder.Pulse_Syntax_Base.binder_ty)
          (FStar_Set.union (freevars initializer1) (freevars_st body))
    | Pulse_Syntax_Base.Tm_Rewrite
        { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;_} ->
        FStar_Set.union (freevars t1) (freevars t2)
    | Pulse_Syntax_Base.Tm_Admit
        { Pulse_Syntax_Base.ctag1 = uu___; Pulse_Syntax_Base.u1 = uu___1;
          Pulse_Syntax_Base.typ = typ; Pulse_Syntax_Base.post3 = post;_}
        -> FStar_Set.union (freevars typ) (freevars_opt post)
    | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
        freevars_st t1
let rec (ln' : Pulse_Syntax_Base.term -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with
      | Pulse_Syntax_Base.Tm_Emp -> true
      | Pulse_Syntax_Base.Tm_VProp -> true
      | Pulse_Syntax_Base.Tm_Inames -> true
      | Pulse_Syntax_Base.Tm_EmpInames -> true
      | Pulse_Syntax_Base.Tm_Unknown -> true
      | Pulse_Syntax_Base.Tm_Star (t1, t2) -> (ln' t1 i) && (ln' t2 i)
      | Pulse_Syntax_Base.Tm_Pure p -> ln' p i
      | Pulse_Syntax_Base.Tm_ExistsSL (uu___, t1, body) ->
          (ln' t1.Pulse_Syntax_Base.binder_ty i) &&
            (ln' body (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_ForallSL (uu___, t1, body) ->
          (ln' t1.Pulse_Syntax_Base.binder_ty i) &&
            (ln' body (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_FStar (t1, uu___) ->
          FStar_Reflection_Typing.ln' t1 i
let (ln_st_comp : Pulse_Syntax_Base.st_comp -> Prims.int -> Prims.bool) =
  fun s ->
    fun i ->
      ((ln' s.Pulse_Syntax_Base.res i) && (ln' s.Pulse_Syntax_Base.pre i)) &&
        (ln' s.Pulse_Syntax_Base.post (i + Prims.int_one))
let (ln_c' : Pulse_Syntax_Base.comp -> Prims.int -> Prims.bool) =
  fun c ->
    fun i ->
      match c with
      | Pulse_Syntax_Base.C_Tot t -> ln' t i
      | Pulse_Syntax_Base.C_ST s -> ln_st_comp s i
      | Pulse_Syntax_Base.C_STAtomic (inames, s) ->
          (ln' inames i) && (ln_st_comp s i)
      | Pulse_Syntax_Base.C_STGhost (inames, s) ->
          (ln' inames i) && (ln_st_comp s i)
let (ln_opt' :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    Prims.int -> Prims.bool)
  =
  fun t ->
    fun i ->
      match t with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some t1 -> ln' t1 i
let rec (ln_list' :
  Pulse_Syntax_Base.term Prims.list -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t with | [] -> true | hd::tl -> (ln' hd i) && (ln_list' tl i)
let rec (ln_st' : Pulse_Syntax_Base.st_term -> Prims.int -> Prims.bool) =
  fun t ->
    fun i ->
      match t.Pulse_Syntax_Base.term1 with
      | Pulse_Syntax_Base.Tm_Return
          { Pulse_Syntax_Base.ctag = uu___;
            Pulse_Syntax_Base.insert_eq = uu___1;
            Pulse_Syntax_Base.term = term;_}
          -> ln' term i
      | Pulse_Syntax_Base.Tm_Abs
          { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = uu___;
            Pulse_Syntax_Base.pre1 = pre; Pulse_Syntax_Base.body = body;
            Pulse_Syntax_Base.ret_ty = ret_ty;
            Pulse_Syntax_Base.post1 = post;_}
          ->
          ((((ln' b.Pulse_Syntax_Base.binder_ty i) &&
               (ln_st' body (i + Prims.int_one)))
              && (ln_opt' pre (i + Prims.int_one)))
             && (ln_opt' ret_ty (i + Prims.int_one)))
            && (ln_opt' post (i + (Prims.of_int (2))))
      | Pulse_Syntax_Base.Tm_STApp
          { Pulse_Syntax_Base.head = head;
            Pulse_Syntax_Base.arg_qual = uu___;
            Pulse_Syntax_Base.arg = arg;_}
          -> (ln' head i) && (ln' arg i)
      | Pulse_Syntax_Base.Tm_Bind
          { Pulse_Syntax_Base.binder = binder;
            Pulse_Syntax_Base.head1 = head; Pulse_Syntax_Base.body1 = body;_}
          ->
          ((ln' binder.Pulse_Syntax_Base.binder_ty i) && (ln_st' head i)) &&
            (ln_st' body (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_TotBind
          { Pulse_Syntax_Base.head2 = head; Pulse_Syntax_Base.body2 = body;_}
          -> (ln' head i) && (ln_st' body (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_If
          { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
            Pulse_Syntax_Base.else_ = else_;
            Pulse_Syntax_Base.post2 = post;_}
          ->
          (((ln' b i) && (ln_st' then_ i)) && (ln_st' else_ i)) &&
            (ln_opt' post (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_IntroPure
          { Pulse_Syntax_Base.p = p;
            Pulse_Syntax_Base.should_check = uu___;_}
          -> ln' p i
      | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p1 = p;_} ->
          ln' p i
      | Pulse_Syntax_Base.Tm_IntroExists
          { Pulse_Syntax_Base.erased = uu___; Pulse_Syntax_Base.p2 = p;
            Pulse_Syntax_Base.witnesses = witnesses;
            Pulse_Syntax_Base.should_check1 = uu___1;_}
          -> (ln' p i) && (ln_list' witnesses i)
      | Pulse_Syntax_Base.Tm_While
          { Pulse_Syntax_Base.invariant = invariant;
            Pulse_Syntax_Base.condition = condition;
            Pulse_Syntax_Base.condition_var = uu___;
            Pulse_Syntax_Base.body3 = body;_}
          ->
          ((ln' invariant (i + Prims.int_one)) && (ln_st' condition i)) &&
            (ln_st' body i)
      | Pulse_Syntax_Base.Tm_Par
          { Pulse_Syntax_Base.pre11 = pre1; Pulse_Syntax_Base.body11 = body1;
            Pulse_Syntax_Base.post11 = post1; Pulse_Syntax_Base.pre2 = pre2;
            Pulse_Syntax_Base.body21 = body2;
            Pulse_Syntax_Base.post21 = post2;_}
          ->
          (((((ln' pre1 i) && (ln_st' body1 i)) &&
               (ln' post1 (i + Prims.int_one)))
              && (ln' pre2 i))
             && (ln_st' body2 i))
            && (ln' post2 (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_WithLocal
          { Pulse_Syntax_Base.binder1 = binder;
            Pulse_Syntax_Base.initializer1 = initializer1;
            Pulse_Syntax_Base.body4 = body;_}
          ->
          ((ln' binder.Pulse_Syntax_Base.binder_ty i) && (ln' initializer1 i))
            && (ln_st' body (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_Rewrite
          { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;_} ->
          (ln' t1 i) && (ln' t2 i)
      | Pulse_Syntax_Base.Tm_Admit
          { Pulse_Syntax_Base.ctag1 = uu___; Pulse_Syntax_Base.u1 = uu___1;
            Pulse_Syntax_Base.typ = typ; Pulse_Syntax_Base.post3 = post;_}
          -> (ln' typ i) && (ln_opt' post (i + Prims.int_one))
      | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
          ln_st' t1 i
let (ln : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t -> ln' t (Prims.of_int (-1))
let (ln_st : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun t -> ln_st' t (Prims.of_int (-1))
let (ln_c : Pulse_Syntax_Base.comp -> Prims.bool) =
  fun c -> ln_c' c (Prims.of_int (-1))
let rec (open_term' :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Pulse_Syntax_Base.Tm_VProp -> t
        | Pulse_Syntax_Base.Tm_Emp -> t
        | Pulse_Syntax_Base.Tm_Inames -> t
        | Pulse_Syntax_Base.Tm_EmpInames -> t
        | Pulse_Syntax_Base.Tm_Unknown -> t
        | Pulse_Syntax_Base.Tm_Pure p ->
            Pulse_Syntax_Base.Tm_Pure (open_term' p v i)
        | Pulse_Syntax_Base.Tm_Star (l, r) ->
            Pulse_Syntax_Base.Tm_Star
              ((open_term' l v i), (open_term' r v i))
        | Pulse_Syntax_Base.Tm_ExistsSL (u, b, body) ->
            Pulse_Syntax_Base.Tm_ExistsSL
              (u,
                {
                  Pulse_Syntax_Base.binder_ty =
                    (open_term' b.Pulse_Syntax_Base.binder_ty v i);
                  Pulse_Syntax_Base.binder_ppname =
                    (b.Pulse_Syntax_Base.binder_ppname)
                }, (open_term' body v (i + Prims.int_one)))
        | Pulse_Syntax_Base.Tm_ForallSL (u, b, body) ->
            Pulse_Syntax_Base.Tm_ForallSL
              (u,
                {
                  Pulse_Syntax_Base.binder_ty =
                    (open_term' b.Pulse_Syntax_Base.binder_ty v i);
                  Pulse_Syntax_Base.binder_ppname =
                    (b.Pulse_Syntax_Base.binder_ppname)
                }, (open_term' body v (i + Prims.int_one)))
        | Pulse_Syntax_Base.Tm_FStar (t1, r) ->
            Pulse_Syntax_Base.Tm_FStar
              ((FStar_Reflection_Typing.open_or_close_term' t1
                  (FStar_Reflection_Typing.OpenWith
                     (Pulse_Elaborate_Pure.elab_term v)) i), r)
let (open_st_comp' :
  Pulse_Syntax_Base.st_comp ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.st_comp)
  =
  fun s ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
          Pulse_Syntax_Base.res = (open_term' s.Pulse_Syntax_Base.res v i);
          Pulse_Syntax_Base.pre = (open_term' s.Pulse_Syntax_Base.pre v i);
          Pulse_Syntax_Base.post =
            (open_term' s.Pulse_Syntax_Base.post v (i + Prims.int_one))
        }
let (open_comp' :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun v ->
      fun i ->
        match c with
        | Pulse_Syntax_Base.C_Tot t ->
            Pulse_Syntax_Base.C_Tot (open_term' t v i)
        | Pulse_Syntax_Base.C_ST s ->
            Pulse_Syntax_Base.C_ST (open_st_comp' s v i)
        | Pulse_Syntax_Base.C_STAtomic (inames, s) ->
            Pulse_Syntax_Base.C_STAtomic
              ((open_term' inames v i), (open_st_comp' s v i))
        | Pulse_Syntax_Base.C_STGhost (inames, s) ->
            Pulse_Syntax_Base.C_STGhost
              ((open_term' inames v i), (open_st_comp' s v i))
let (open_term_opt' :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index ->
        Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t1 ->
            FStar_Pervasives_Native.Some (open_term' t1 v i)
let rec (open_term_list' :
  Pulse_Syntax_Base.term Prims.list ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term Prims.list)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | [] -> []
        | hd::tl -> (open_term' hd v i) :: (open_term_list' tl v i)
let (open_binder :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.binder)
  =
  fun b ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax_Base.binder_ty =
            (open_term' b.Pulse_Syntax_Base.binder_ty v i);
          Pulse_Syntax_Base.binder_ppname =
            (b.Pulse_Syntax_Base.binder_ppname)
        }
let rec (open_st_term' :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    fun v ->
      fun i ->
        let t' =
          match t.Pulse_Syntax_Base.term1 with
          | Pulse_Syntax_Base.Tm_Return
              { Pulse_Syntax_Base.ctag = ctag;
                Pulse_Syntax_Base.insert_eq = insert_eq;
                Pulse_Syntax_Base.term = term;_}
              ->
              Pulse_Syntax_Base.Tm_Return
                {
                  Pulse_Syntax_Base.ctag = ctag;
                  Pulse_Syntax_Base.insert_eq = insert_eq;
                  Pulse_Syntax_Base.term = (open_term' term v i)
                }
          | Pulse_Syntax_Base.Tm_Abs
              { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                Pulse_Syntax_Base.pre1 = pre; Pulse_Syntax_Base.body = body;
                Pulse_Syntax_Base.ret_ty = ret_ty;
                Pulse_Syntax_Base.post1 = post;_}
              ->
              Pulse_Syntax_Base.Tm_Abs
                {
                  Pulse_Syntax_Base.b = (open_binder b v i);
                  Pulse_Syntax_Base.q = q;
                  Pulse_Syntax_Base.pre1 =
                    (open_term_opt' pre v (i + Prims.int_one));
                  Pulse_Syntax_Base.body =
                    (open_st_term' body v (i + Prims.int_one));
                  Pulse_Syntax_Base.ret_ty =
                    (open_term_opt' ret_ty v (i + Prims.int_one));
                  Pulse_Syntax_Base.post1 =
                    (open_term_opt' post v (i + (Prims.of_int (2))))
                }
          | Pulse_Syntax_Base.Tm_STApp
              { Pulse_Syntax_Base.head = head;
                Pulse_Syntax_Base.arg_qual = arg_qual;
                Pulse_Syntax_Base.arg = arg;_}
              ->
              Pulse_Syntax_Base.Tm_STApp
                {
                  Pulse_Syntax_Base.head = (open_term' head v i);
                  Pulse_Syntax_Base.arg_qual = arg_qual;
                  Pulse_Syntax_Base.arg = (open_term' arg v i)
                }
          | Pulse_Syntax_Base.Tm_Bind
              { Pulse_Syntax_Base.binder = binder;
                Pulse_Syntax_Base.head1 = head;
                Pulse_Syntax_Base.body1 = body;_}
              ->
              Pulse_Syntax_Base.Tm_Bind
                {
                  Pulse_Syntax_Base.binder = (open_binder binder v i);
                  Pulse_Syntax_Base.head1 = (open_st_term' head v i);
                  Pulse_Syntax_Base.body1 =
                    (open_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_TotBind
              { Pulse_Syntax_Base.head2 = head;
                Pulse_Syntax_Base.body2 = body;_}
              ->
              Pulse_Syntax_Base.Tm_TotBind
                {
                  Pulse_Syntax_Base.head2 = (open_term' head v i);
                  Pulse_Syntax_Base.body2 =
                    (open_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_If
              { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
                Pulse_Syntax_Base.else_ = else_;
                Pulse_Syntax_Base.post2 = post;_}
              ->
              Pulse_Syntax_Base.Tm_If
                {
                  Pulse_Syntax_Base.b1 = (open_term' b v i);
                  Pulse_Syntax_Base.then_ = (open_st_term' then_ v i);
                  Pulse_Syntax_Base.else_ = (open_st_term' else_ v i);
                  Pulse_Syntax_Base.post2 =
                    (open_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_IntroPure
              { Pulse_Syntax_Base.p = p;
                Pulse_Syntax_Base.should_check = should_check;_}
              ->
              Pulse_Syntax_Base.Tm_IntroPure
                {
                  Pulse_Syntax_Base.p = (open_term' p v i);
                  Pulse_Syntax_Base.should_check = should_check
                }
          | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p1 = p;_} ->
              Pulse_Syntax_Base.Tm_ElimExists
                { Pulse_Syntax_Base.p1 = (open_term' p v i) }
          | Pulse_Syntax_Base.Tm_IntroExists
              { Pulse_Syntax_Base.erased = erased; Pulse_Syntax_Base.p2 = p;
                Pulse_Syntax_Base.witnesses = witnesses;
                Pulse_Syntax_Base.should_check1 = should_check;_}
              ->
              Pulse_Syntax_Base.Tm_IntroExists
                {
                  Pulse_Syntax_Base.erased = erased;
                  Pulse_Syntax_Base.p2 = (open_term' p v i);
                  Pulse_Syntax_Base.witnesses =
                    (open_term_list' witnesses v i);
                  Pulse_Syntax_Base.should_check1 = should_check
                }
          | Pulse_Syntax_Base.Tm_While
              { Pulse_Syntax_Base.invariant = invariant;
                Pulse_Syntax_Base.condition = condition;
                Pulse_Syntax_Base.condition_var = condition_var;
                Pulse_Syntax_Base.body3 = body;_}
              ->
              Pulse_Syntax_Base.Tm_While
                {
                  Pulse_Syntax_Base.invariant =
                    (open_term' invariant v (i + Prims.int_one));
                  Pulse_Syntax_Base.condition = (open_st_term' condition v i);
                  Pulse_Syntax_Base.condition_var = condition_var;
                  Pulse_Syntax_Base.body3 = (open_st_term' body v i)
                }
          | Pulse_Syntax_Base.Tm_Par
              { Pulse_Syntax_Base.pre11 = pre1;
                Pulse_Syntax_Base.body11 = body1;
                Pulse_Syntax_Base.post11 = post1;
                Pulse_Syntax_Base.pre2 = pre2;
                Pulse_Syntax_Base.body21 = body2;
                Pulse_Syntax_Base.post21 = post2;_}
              ->
              Pulse_Syntax_Base.Tm_Par
                {
                  Pulse_Syntax_Base.pre11 = (open_term' pre1 v i);
                  Pulse_Syntax_Base.body11 = (open_st_term' body1 v i);
                  Pulse_Syntax_Base.post11 =
                    (open_term' post1 v (i + Prims.int_one));
                  Pulse_Syntax_Base.pre2 = (open_term' pre2 v i);
                  Pulse_Syntax_Base.body21 = (open_st_term' body2 v i);
                  Pulse_Syntax_Base.post21 =
                    (open_term' post2 v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_WithLocal
              { Pulse_Syntax_Base.binder1 = binder;
                Pulse_Syntax_Base.initializer1 = initializer1;
                Pulse_Syntax_Base.body4 = body;_}
              ->
              Pulse_Syntax_Base.Tm_WithLocal
                {
                  Pulse_Syntax_Base.binder1 = (open_binder binder v i);
                  Pulse_Syntax_Base.initializer1 =
                    (open_term' initializer1 v i);
                  Pulse_Syntax_Base.body4 =
                    (open_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_Rewrite
              { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;_} ->
              Pulse_Syntax_Base.Tm_Rewrite
                {
                  Pulse_Syntax_Base.t1 = (open_term' t1 v i);
                  Pulse_Syntax_Base.t2 = (open_term' t2 v i)
                }
          | Pulse_Syntax_Base.Tm_Admit
              { Pulse_Syntax_Base.ctag1 = ctag; Pulse_Syntax_Base.u1 = u;
                Pulse_Syntax_Base.typ = typ;
                Pulse_Syntax_Base.post3 = post;_}
              ->
              Pulse_Syntax_Base.Tm_Admit
                {
                  Pulse_Syntax_Base.ctag1 = ctag;
                  Pulse_Syntax_Base.u1 = u;
                  Pulse_Syntax_Base.typ = (open_term' typ v i);
                  Pulse_Syntax_Base.post3 =
                    (open_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
              Pulse_Syntax_Base.Tm_Protect
                { Pulse_Syntax_Base.t = (open_st_term' t1 v i) } in
        {
          Pulse_Syntax_Base.term1 = t';
          Pulse_Syntax_Base.range1 = (t.Pulse_Syntax_Base.range1)
        }
let (open_term_nv :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun nv -> open_term' t (Pulse_Syntax_Pure.term_of_nvar nv) Prims.int_zero
let (open_st_term_nv :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    fun nv ->
      open_st_term' t (Pulse_Syntax_Pure.term_of_nvar nv) Prims.int_zero
let (open_comp_with :
  Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  = fun c -> fun x -> open_comp' c x Prims.int_zero
let rec (close_term' :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | Pulse_Syntax_Base.Tm_VProp -> t
        | Pulse_Syntax_Base.Tm_Emp -> t
        | Pulse_Syntax_Base.Tm_Inames -> t
        | Pulse_Syntax_Base.Tm_EmpInames -> t
        | Pulse_Syntax_Base.Tm_Unknown -> t
        | Pulse_Syntax_Base.Tm_Pure p ->
            Pulse_Syntax_Base.Tm_Pure (close_term' p v i)
        | Pulse_Syntax_Base.Tm_Star (l, r) ->
            Pulse_Syntax_Base.Tm_Star
              ((close_term' l v i), (close_term' r v i))
        | Pulse_Syntax_Base.Tm_ExistsSL (u, b, body) ->
            Pulse_Syntax_Base.Tm_ExistsSL
              (u,
                {
                  Pulse_Syntax_Base.binder_ty =
                    (close_term' b.Pulse_Syntax_Base.binder_ty v i);
                  Pulse_Syntax_Base.binder_ppname =
                    (b.Pulse_Syntax_Base.binder_ppname)
                }, (close_term' body v (i + Prims.int_one)))
        | Pulse_Syntax_Base.Tm_ForallSL (u, b, body) ->
            Pulse_Syntax_Base.Tm_ForallSL
              (u,
                {
                  Pulse_Syntax_Base.binder_ty =
                    (close_term' b.Pulse_Syntax_Base.binder_ty v i);
                  Pulse_Syntax_Base.binder_ppname =
                    (b.Pulse_Syntax_Base.binder_ppname)
                }, (close_term' body v (i + Prims.int_one)))
        | Pulse_Syntax_Base.Tm_FStar (t1, r) ->
            Pulse_Syntax_Base.Tm_FStar
              ((FStar_Reflection_Typing.open_or_close_term' t1
                  (FStar_Reflection_Typing.CloseVar v) i), r)
let (close_st_comp' :
  Pulse_Syntax_Base.st_comp ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.st_comp)
  =
  fun s ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
          Pulse_Syntax_Base.res = (close_term' s.Pulse_Syntax_Base.res v i);
          Pulse_Syntax_Base.pre = (close_term' s.Pulse_Syntax_Base.pre v i);
          Pulse_Syntax_Base.post =
            (close_term' s.Pulse_Syntax_Base.post v (i + Prims.int_one))
        }
let (close_comp' :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun v ->
      fun i ->
        match c with
        | Pulse_Syntax_Base.C_Tot t ->
            Pulse_Syntax_Base.C_Tot (close_term' t v i)
        | Pulse_Syntax_Base.C_ST s ->
            Pulse_Syntax_Base.C_ST (close_st_comp' s v i)
        | Pulse_Syntax_Base.C_STAtomic (inames, s) ->
            Pulse_Syntax_Base.C_STAtomic
              ((close_term' inames v i), (close_st_comp' s v i))
        | Pulse_Syntax_Base.C_STGhost (inames, s) ->
            Pulse_Syntax_Base.C_STGhost
              ((close_term' inames v i), (close_st_comp' s v i))
let (close_term_opt' :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index ->
        Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t1 ->
            FStar_Pervasives_Native.Some (close_term' t1 v i)
let rec (close_term_list' :
  Pulse_Syntax_Base.term Prims.list ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term Prims.list)
  =
  fun t ->
    fun v ->
      fun i ->
        match t with
        | [] -> []
        | hd::tl -> (close_term' hd v i) :: (close_term_list' tl v i)
let (close_binder :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.binder)
  =
  fun b ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax_Base.binder_ty =
            (close_term' b.Pulse_Syntax_Base.binder_ty v i);
          Pulse_Syntax_Base.binder_ppname =
            (b.Pulse_Syntax_Base.binder_ppname)
        }
let rec (close_st_term' :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    fun v ->
      fun i ->
        let t' =
          match t.Pulse_Syntax_Base.term1 with
          | Pulse_Syntax_Base.Tm_Return
              { Pulse_Syntax_Base.ctag = ctag;
                Pulse_Syntax_Base.insert_eq = insert_eq;
                Pulse_Syntax_Base.term = term;_}
              ->
              Pulse_Syntax_Base.Tm_Return
                {
                  Pulse_Syntax_Base.ctag = ctag;
                  Pulse_Syntax_Base.insert_eq = insert_eq;
                  Pulse_Syntax_Base.term = (close_term' term v i)
                }
          | Pulse_Syntax_Base.Tm_Abs
              { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                Pulse_Syntax_Base.pre1 = pre; Pulse_Syntax_Base.body = body;
                Pulse_Syntax_Base.ret_ty = ret_ty;
                Pulse_Syntax_Base.post1 = post;_}
              ->
              Pulse_Syntax_Base.Tm_Abs
                {
                  Pulse_Syntax_Base.b = (close_binder b v i);
                  Pulse_Syntax_Base.q = q;
                  Pulse_Syntax_Base.pre1 =
                    (close_term_opt' pre v (i + Prims.int_one));
                  Pulse_Syntax_Base.body =
                    (close_st_term' body v (i + Prims.int_one));
                  Pulse_Syntax_Base.ret_ty =
                    (close_term_opt' ret_ty v (i + Prims.int_one));
                  Pulse_Syntax_Base.post1 =
                    (close_term_opt' post v (i + (Prims.of_int (2))))
                }
          | Pulse_Syntax_Base.Tm_STApp
              { Pulse_Syntax_Base.head = head;
                Pulse_Syntax_Base.arg_qual = arg_qual;
                Pulse_Syntax_Base.arg = arg;_}
              ->
              Pulse_Syntax_Base.Tm_STApp
                {
                  Pulse_Syntax_Base.head = (close_term' head v i);
                  Pulse_Syntax_Base.arg_qual = arg_qual;
                  Pulse_Syntax_Base.arg = (close_term' arg v i)
                }
          | Pulse_Syntax_Base.Tm_Bind
              { Pulse_Syntax_Base.binder = binder;
                Pulse_Syntax_Base.head1 = head;
                Pulse_Syntax_Base.body1 = body;_}
              ->
              Pulse_Syntax_Base.Tm_Bind
                {
                  Pulse_Syntax_Base.binder = (close_binder binder v i);
                  Pulse_Syntax_Base.head1 = (close_st_term' head v i);
                  Pulse_Syntax_Base.body1 =
                    (close_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_TotBind
              { Pulse_Syntax_Base.head2 = head;
                Pulse_Syntax_Base.body2 = body;_}
              ->
              Pulse_Syntax_Base.Tm_TotBind
                {
                  Pulse_Syntax_Base.head2 = (close_term' head v i);
                  Pulse_Syntax_Base.body2 =
                    (close_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_If
              { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
                Pulse_Syntax_Base.else_ = else_;
                Pulse_Syntax_Base.post2 = post;_}
              ->
              Pulse_Syntax_Base.Tm_If
                {
                  Pulse_Syntax_Base.b1 = (close_term' b v i);
                  Pulse_Syntax_Base.then_ = (close_st_term' then_ v i);
                  Pulse_Syntax_Base.else_ = (close_st_term' else_ v i);
                  Pulse_Syntax_Base.post2 =
                    (close_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_IntroPure
              { Pulse_Syntax_Base.p = p;
                Pulse_Syntax_Base.should_check = should_check;_}
              ->
              Pulse_Syntax_Base.Tm_IntroPure
                {
                  Pulse_Syntax_Base.p = (close_term' p v i);
                  Pulse_Syntax_Base.should_check = should_check
                }
          | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p1 = p;_} ->
              Pulse_Syntax_Base.Tm_ElimExists
                { Pulse_Syntax_Base.p1 = (close_term' p v i) }
          | Pulse_Syntax_Base.Tm_IntroExists
              { Pulse_Syntax_Base.erased = erased; Pulse_Syntax_Base.p2 = p;
                Pulse_Syntax_Base.witnesses = witnesses;
                Pulse_Syntax_Base.should_check1 = should_check;_}
              ->
              Pulse_Syntax_Base.Tm_IntroExists
                {
                  Pulse_Syntax_Base.erased = erased;
                  Pulse_Syntax_Base.p2 = (close_term' p v i);
                  Pulse_Syntax_Base.witnesses =
                    (close_term_list' witnesses v i);
                  Pulse_Syntax_Base.should_check1 = should_check
                }
          | Pulse_Syntax_Base.Tm_While
              { Pulse_Syntax_Base.invariant = invariant;
                Pulse_Syntax_Base.condition = condition;
                Pulse_Syntax_Base.condition_var = condition_var;
                Pulse_Syntax_Base.body3 = body;_}
              ->
              Pulse_Syntax_Base.Tm_While
                {
                  Pulse_Syntax_Base.invariant =
                    (close_term' invariant v (i + Prims.int_one));
                  Pulse_Syntax_Base.condition =
                    (close_st_term' condition v i);
                  Pulse_Syntax_Base.condition_var = condition_var;
                  Pulse_Syntax_Base.body3 = (close_st_term' body v i)
                }
          | Pulse_Syntax_Base.Tm_Par
              { Pulse_Syntax_Base.pre11 = pre1;
                Pulse_Syntax_Base.body11 = body1;
                Pulse_Syntax_Base.post11 = post1;
                Pulse_Syntax_Base.pre2 = pre2;
                Pulse_Syntax_Base.body21 = body2;
                Pulse_Syntax_Base.post21 = post2;_}
              ->
              Pulse_Syntax_Base.Tm_Par
                {
                  Pulse_Syntax_Base.pre11 = (close_term' pre1 v i);
                  Pulse_Syntax_Base.body11 = (close_st_term' body1 v i);
                  Pulse_Syntax_Base.post11 =
                    (close_term' post1 v (i + Prims.int_one));
                  Pulse_Syntax_Base.pre2 = (close_term' pre2 v i);
                  Pulse_Syntax_Base.body21 = (close_st_term' body2 v i);
                  Pulse_Syntax_Base.post21 =
                    (close_term' post2 v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_WithLocal
              { Pulse_Syntax_Base.binder1 = binder;
                Pulse_Syntax_Base.initializer1 = initializer1;
                Pulse_Syntax_Base.body4 = body;_}
              ->
              Pulse_Syntax_Base.Tm_WithLocal
                {
                  Pulse_Syntax_Base.binder1 = (close_binder binder v i);
                  Pulse_Syntax_Base.initializer1 =
                    (close_term' initializer1 v i);
                  Pulse_Syntax_Base.body4 =
                    (close_st_term' body v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_Rewrite
              { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;_} ->
              Pulse_Syntax_Base.Tm_Rewrite
                {
                  Pulse_Syntax_Base.t1 = (close_term' t1 v i);
                  Pulse_Syntax_Base.t2 = (close_term' t2 v i)
                }
          | Pulse_Syntax_Base.Tm_Admit
              { Pulse_Syntax_Base.ctag1 = ctag; Pulse_Syntax_Base.u1 = u;
                Pulse_Syntax_Base.typ = typ;
                Pulse_Syntax_Base.post3 = post;_}
              ->
              Pulse_Syntax_Base.Tm_Admit
                {
                  Pulse_Syntax_Base.ctag1 = ctag;
                  Pulse_Syntax_Base.u1 = u;
                  Pulse_Syntax_Base.typ = (close_term' typ v i);
                  Pulse_Syntax_Base.post3 =
                    (close_term_opt' post v (i + Prims.int_one))
                }
          | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
              Pulse_Syntax_Base.Tm_Protect
                { Pulse_Syntax_Base.t = (close_st_term' t1 v i) } in
        {
          Pulse_Syntax_Base.term1 = t';
          Pulse_Syntax_Base.range1 = (t.Pulse_Syntax_Base.range1)
        }
let (close_term :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term)
  = fun t -> fun v -> close_term' t v Prims.int_zero
let (close_st_term :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.var -> Pulse_Syntax_Base.st_term)
  = fun t -> fun v -> close_st_term' t v Prims.int_zero
let (close_comp :
  Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.comp)
  = fun t -> fun v -> close_comp' t v Prims.int_zero