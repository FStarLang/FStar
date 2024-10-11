open Prims
let map_opt :
  'uuuuu 'uuuuu1 .
    'uuuuu FStar_Pervasives_Native.option ->
      ('uuuuu -> 'uuuuu1) -> 'uuuuu1 FStar_Pervasives_Native.option
  =
  fun o ->
    fun f ->
      match o with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some (f x)
let (thunk : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun t ->
    let b =
      FStarC_Reflection_V2_Builtins.pack_binder
        {
          FStarC_Reflection_V2_Data.sort2 =
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"])));
          FStarC_Reflection_V2_Data.qual = FStarC_Reflection_V2_Data.Q_Explicit;
          FStarC_Reflection_V2_Data.attrs = [];
          FStarC_Reflection_V2_Data.ppname2 = (FStar_Sealed.seal "_")
        } in
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_Abs (b, t))
let (pat_var :
  FStar_Reflection_Typing.pp_name_t ->
    FStar_Reflection_Typing.sort_t -> Pulse_Syntax_Base.pattern)
  = fun s -> fun uu___ -> Pulse_Syntax_Base.Pat_Var (s, uu___)
let (pat_const : Pulse_Syntax_Base.constant -> Pulse_Syntax_Base.pattern) =
  fun c -> Pulse_Syntax_Base.Pat_Constant c
let (pat_cons :
  Pulse_Syntax_Base.fv ->
    (Pulse_Syntax_Base.pattern * Prims.bool) Prims.list ->
      Pulse_Syntax_Base.pattern)
  = fun fv -> fun vs -> Pulse_Syntax_Base.Pat_Cons (fv, vs)
let (tm_return :
  Pulse_Syntax_Base.term ->
    Prims.bool -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term')
  =
  fun expected_type ->
    fun insert_eq ->
      fun term ->
        Pulse_Syntax_Base.Tm_Return
          {
            Pulse_Syntax_Base.expected_type = expected_type;
            Pulse_Syntax_Base.insert_eq = insert_eq;
            Pulse_Syntax_Base.term = term
          }
let (tm_abs :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.comp_ascription ->
        Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term')
  =
  fun b ->
    fun q ->
      fun ascription ->
        fun body ->
          Pulse_Syntax_Base.Tm_Abs
            {
              Pulse_Syntax_Base.b = b;
              Pulse_Syntax_Base.q = q;
              Pulse_Syntax_Base.ascription = ascription;
              Pulse_Syntax_Base.body = body
            }
let (tm_stapp :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term')
  =
  fun head ->
    fun arg_qual ->
      fun arg ->
        Pulse_Syntax_Base.Tm_STApp
          {
            Pulse_Syntax_Base.head = head;
            Pulse_Syntax_Base.arg_qual = arg_qual;
            Pulse_Syntax_Base.arg = arg
          }
let (tm_bind :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term')
  =
  fun binder ->
    fun head ->
      fun body ->
        Pulse_Syntax_Base.Tm_Bind
          {
            Pulse_Syntax_Base.binder = binder;
            Pulse_Syntax_Base.head1 = head;
            Pulse_Syntax_Base.body1 = body
          }
let (tm_totbind :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term')
  =
  fun binder ->
    fun head ->
      fun body ->
        Pulse_Syntax_Base.Tm_TotBind
          {
            Pulse_Syntax_Base.binder1 = binder;
            Pulse_Syntax_Base.head2 = head;
            Pulse_Syntax_Base.body2 = body
          }
let (tm_if :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.slprop FStar_Pervasives_Native.option ->
          Pulse_Syntax_Base.st_term')
  =
  fun b ->
    fun then_ ->
      fun else_ ->
        fun post ->
          Pulse_Syntax_Base.Tm_If
            {
              Pulse_Syntax_Base.b1 = b;
              Pulse_Syntax_Base.then_ = then_;
              Pulse_Syntax_Base.else_ = else_;
              Pulse_Syntax_Base.post1 = post
            }
let (tm_match :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.slprop FStar_Pervasives_Native.option ->
      (Pulse_Syntax_Base.pattern * Pulse_Syntax_Base.st_term) Prims.list ->
        Pulse_Syntax_Base.st_term')
  =
  fun sc ->
    fun returns_ ->
      fun brs ->
        Pulse_Syntax_Base.Tm_Match
          {
            Pulse_Syntax_Base.sc = sc;
            Pulse_Syntax_Base.returns_ = returns_;
            Pulse_Syntax_Base.brs = brs
          }
let (tm_elim_exists : Pulse_Syntax_Base.slprop -> Pulse_Syntax_Base.st_term')
  = fun p -> Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p4 = p }
let (tm_intro_exists :
  Pulse_Syntax_Base.slprop ->
    Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.st_term')
  =
  fun p ->
    fun witnesses ->
      Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.p5 = p; Pulse_Syntax_Base.witnesses = witnesses }
let (tm_while :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.ppname ->
        Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term')
  =
  fun invariant ->
    fun condition ->
      fun condition_var ->
        fun body ->
          Pulse_Syntax_Base.Tm_While
            {
              Pulse_Syntax_Base.invariant = invariant;
              Pulse_Syntax_Base.condition = condition;
              Pulse_Syntax_Base.condition_var = condition_var;
              Pulse_Syntax_Base.body3 = body
            }
let (tm_par :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term')
  =
  fun pre1 ->
    fun body1 ->
      fun post1 ->
        fun pre2 ->
          fun body2 ->
            fun post2 ->
              Pulse_Syntax_Base.Tm_Par
                {
                  Pulse_Syntax_Base.pre1 = pre1;
                  Pulse_Syntax_Base.body11 = body1;
                  Pulse_Syntax_Base.post11 = post1;
                  Pulse_Syntax_Base.pre2 = pre2;
                  Pulse_Syntax_Base.body21 = body2;
                  Pulse_Syntax_Base.post2 = post2
                }
let (tm_with_inv :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.binder * Pulse_Syntax_Base.slprop *
        Pulse_Syntax_Base.term) FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.st_term')
  =
  fun name ->
    fun body ->
      fun returns_inv ->
        Pulse_Syntax_Base.Tm_WithInv
          {
            Pulse_Syntax_Base.name1 = name;
            Pulse_Syntax_Base.body6 = body;
            Pulse_Syntax_Base.returns_inv = returns_inv
          }
let tm_add_inv :
  'uuuuu .
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term -> 'uuuuu -> FStarC_Reflection_Types.term
  = fun names -> fun n -> fun r -> Pulse_Syntax_Pure.tm_add_inv names n
let (tm_with_local :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term')
  =
  fun binder ->
    fun initializer1 ->
      fun body ->
        Pulse_Syntax_Base.Tm_WithLocal
          {
            Pulse_Syntax_Base.binder2 = binder;
            Pulse_Syntax_Base.initializer1 = initializer1;
            Pulse_Syntax_Base.body4 = body
          }
let (tm_with_local_array :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term')
  =
  fun binder ->
    fun initializer1 ->
      fun length ->
        fun body ->
          Pulse_Syntax_Base.Tm_WithLocalArray
            {
              Pulse_Syntax_Base.binder3 = binder;
              Pulse_Syntax_Base.initializer2 = initializer1;
              Pulse_Syntax_Base.length = length;
              Pulse_Syntax_Base.body5 = body
            }
let (tm_admit :
  Pulse_Syntax_Base.ctag ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
          Pulse_Syntax_Base.st_term')
  =
  fun ctag ->
    fun u ->
      fun typ ->
        fun post ->
          Pulse_Syntax_Base.Tm_Admit
            {
              Pulse_Syntax_Base.ctag = ctag;
              Pulse_Syntax_Base.u1 = u;
              Pulse_Syntax_Base.typ = typ;
              Pulse_Syntax_Base.post3 = post
            }
let (tm_unreachable :
  Pulse_Syntax_Base.st_term'__Tm_Unreachable__payload ->
    Pulse_Syntax_Base.st_term')
  = fun uu___ -> Pulse_Syntax_Base.Tm_Unreachable uu___
let (with_range :
  Pulse_Syntax_Base.st_term' ->
    Pulse_Syntax_Base.range -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    fun r ->
      {
        Pulse_Syntax_Base.term1 = t;
        Pulse_Syntax_Base.range1 = r;
        Pulse_Syntax_Base.effect_tag = Pulse_Syntax_Base.default_effect_hint;
        Pulse_Syntax_Base.source = (FStar_Sealed.seal true)
      }
let (tm_assert_with_binders :
  Pulse_Syntax_Base.binder Prims.list ->
    Pulse_Syntax_Base.slprop ->
      Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term')
  =
  fun bs ->
    fun p ->
      fun t ->
        Pulse_Syntax_Base.Tm_ProofHintWithBinders
          {
            Pulse_Syntax_Base.hint_type =
              (Pulse_Syntax_Base.ASSERT { Pulse_Syntax_Base.p = p });
            Pulse_Syntax_Base.binders = bs;
            Pulse_Syntax_Base.t = t
          }
let (mk_assert_hint_type :
  Pulse_Syntax_Base.slprop -> Pulse_Syntax_Base.proof_hint_type) =
  fun p -> Pulse_Syntax_Base.ASSERT { Pulse_Syntax_Base.p = p }
let (mk_unfold_hint_type :
  Prims.string Prims.list FStar_Pervasives_Native.option ->
    Pulse_Syntax_Base.slprop -> Pulse_Syntax_Base.proof_hint_type)
  =
  fun names ->
    fun p ->
      Pulse_Syntax_Base.UNFOLD
        { Pulse_Syntax_Base.names1 = names; Pulse_Syntax_Base.p2 = p }
let (mk_fold_hint_type :
  Prims.string Prims.list FStar_Pervasives_Native.option ->
    Pulse_Syntax_Base.slprop -> Pulse_Syntax_Base.proof_hint_type)
  =
  fun names ->
    fun p ->
      Pulse_Syntax_Base.FOLD
        { Pulse_Syntax_Base.names = names; Pulse_Syntax_Base.p1 = p }
let (mk_rename_hint_type :
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.proof_hint_type)
  =
  fun pairs ->
    fun goal ->
      fun tac_opt ->
        Pulse_Syntax_Base.RENAME
          {
            Pulse_Syntax_Base.pairs = pairs;
            Pulse_Syntax_Base.goal = goal;
            Pulse_Syntax_Base.tac_opt = (map_opt tac_opt thunk)
          }
let (mk_rewrite_hint_type :
  Pulse_Syntax_Base.slprop ->
    Pulse_Syntax_Base.slprop ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.proof_hint_type)
  =
  fun t1 ->
    fun t2 ->
      fun tac_opt ->
        Pulse_Syntax_Base.REWRITE
          {
            Pulse_Syntax_Base.t1 = t1;
            Pulse_Syntax_Base.t2 = t2;
            Pulse_Syntax_Base.tac_opt1 = (map_opt tac_opt thunk)
          }
let (mk_fn_defn :
  FStarC_Reflection_Types.ident ->
    Prims.bool ->
      (Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
        Pulse_Syntax_Base.binder * Pulse_Syntax_Base.bv) Prims.list ->
        Pulse_Syntax_Base.comp ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.decl')
  =
  fun id ->
    fun isrec ->
      fun bs ->
        fun comp ->
          fun meas ->
            fun body ->
              Pulse_Syntax_Base.FnDefn
                {
                  Pulse_Syntax_Base.id = id;
                  Pulse_Syntax_Base.isrec = isrec;
                  Pulse_Syntax_Base.bs = bs;
                  Pulse_Syntax_Base.comp = comp;
                  Pulse_Syntax_Base.meas = meas;
                  Pulse_Syntax_Base.body7 = body
                }
let (mk_fn_decl :
  FStarC_Reflection_Types.ident ->
    (Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
      Pulse_Syntax_Base.binder * Pulse_Syntax_Base.bv) Prims.list ->
      Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.decl')
  =
  fun id ->
    fun bs ->
      fun comp ->
        Pulse_Syntax_Base.FnDecl
          {
            Pulse_Syntax_Base.id1 = id;
            Pulse_Syntax_Base.bs1 = bs;
            Pulse_Syntax_Base.comp1 = comp
          }
let (mk_decl :
  Pulse_Syntax_Base.decl' ->
    Pulse_Syntax_Base.range -> Pulse_Syntax_Base.decl)
  =
  fun d ->
    fun range ->
      { Pulse_Syntax_Base.d = d; Pulse_Syntax_Base.range2 = range }