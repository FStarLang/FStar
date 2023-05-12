open Prims
let (tm_return :
  Pulse_Syntax.ctag ->
    Prims.bool -> Pulse_Syntax.term -> Pulse_Syntax.st_term')
  =
  fun ctag ->
    fun insert_eq ->
      fun term ->
        Pulse_Syntax.Tm_Return
          {
            Pulse_Syntax.ctag = ctag;
            Pulse_Syntax.insert_eq = insert_eq;
            Pulse_Syntax.term = term
          }
let (tm_abs :
  Pulse_Syntax.binder ->
    Pulse_Syntax.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax.vprop FStar_Pervasives_Native.option ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.vprop FStar_Pervasives_Native.option ->
            Pulse_Syntax.st_term')
  =
  fun b ->
    fun q ->
      fun pre ->
        fun body ->
          fun post ->
            Pulse_Syntax.Tm_Abs
              {
                Pulse_Syntax.b = b;
                Pulse_Syntax.q = q;
                Pulse_Syntax.pre1 = pre;
                Pulse_Syntax.body = body;
                Pulse_Syntax.post1 = post
              }
let (tm_stapp :
  Pulse_Syntax.term ->
    Pulse_Syntax.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax.term -> Pulse_Syntax.st_term')
  =
  fun head ->
    fun arg_qual ->
      fun arg ->
        Pulse_Syntax.Tm_STApp
          {
            Pulse_Syntax.head = head;
            Pulse_Syntax.arg_qual = arg_qual;
            Pulse_Syntax.arg = arg
          }
let (tm_bind :
  Pulse_Syntax.binder ->
    Pulse_Syntax.st_term -> Pulse_Syntax.st_term -> Pulse_Syntax.st_term')
  =
  fun binder ->
    fun head ->
      fun body ->
        Pulse_Syntax.Tm_Bind
          {
            Pulse_Syntax.binder = binder;
            Pulse_Syntax.head1 = head;
            Pulse_Syntax.body1 = body
          }
let (tm_totbind :
  Pulse_Syntax.term -> Pulse_Syntax.st_term -> Pulse_Syntax.st_term') =
  fun head ->
    fun body ->
      Pulse_Syntax.Tm_TotBind
        { Pulse_Syntax.head2 = head; Pulse_Syntax.body2 = body }
let (tm_if :
  Pulse_Syntax.term ->
    Pulse_Syntax.st_term ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.vprop FStar_Pervasives_Native.option ->
          Pulse_Syntax.st_term')
  =
  fun b ->
    fun then_ ->
      fun else_ ->
        fun post ->
          Pulse_Syntax.Tm_If
            {
              Pulse_Syntax.b1 = b;
              Pulse_Syntax.then_ = then_;
              Pulse_Syntax.else_ = else_;
              Pulse_Syntax.post2 = post
            }
let (tm_elim_exists : Pulse_Syntax.vprop -> Pulse_Syntax.st_term') =
  fun p -> Pulse_Syntax.Tm_ElimExists { Pulse_Syntax.p = p }
let (tm_intro_exists :
  Prims.bool ->
    Pulse_Syntax.vprop ->
      Pulse_Syntax.term Prims.list -> Pulse_Syntax.st_term')
  =
  fun erased ->
    fun p ->
      fun witnesses ->
        Pulse_Syntax.Tm_IntroExists
          {
            Pulse_Syntax.erased = erased;
            Pulse_Syntax.p1 = p;
            Pulse_Syntax.witnesses = witnesses
          }
let (tm_while :
  Pulse_Syntax.term ->
    Pulse_Syntax.st_term -> Pulse_Syntax.st_term -> Pulse_Syntax.st_term')
  =
  fun invariant ->
    fun condition ->
      fun body ->
        Pulse_Syntax.Tm_While
          {
            Pulse_Syntax.invariant = invariant;
            Pulse_Syntax.condition = condition;
            Pulse_Syntax.body3 = body
          }
let (tm_par :
  Pulse_Syntax.term ->
    Pulse_Syntax.st_term ->
      Pulse_Syntax.term ->
        Pulse_Syntax.term ->
          Pulse_Syntax.st_term -> Pulse_Syntax.term -> Pulse_Syntax.st_term')
  =
  fun pre1 ->
    fun body1 ->
      fun post1 ->
        fun pre2 ->
          fun body2 ->
            fun post2 ->
              Pulse_Syntax.Tm_Par
                {
                  Pulse_Syntax.pre11 = pre1;
                  Pulse_Syntax.body11 = body1;
                  Pulse_Syntax.post11 = post1;
                  Pulse_Syntax.pre2 = pre2;
                  Pulse_Syntax.body21 = body2;
                  Pulse_Syntax.post21 = post2
                }
let (tm_with_local :
  Pulse_Syntax.term -> Pulse_Syntax.st_term -> Pulse_Syntax.st_term') =
  fun initializer1 ->
    fun body ->
      Pulse_Syntax.Tm_WithLocal
        { Pulse_Syntax.initializer1 = initializer1; Pulse_Syntax.body4 = body
        }
let (tm_rewrite :
  Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.st_term') =
  fun t1 ->
    fun t2 ->
      Pulse_Syntax.Tm_Rewrite { Pulse_Syntax.t1 = t1; Pulse_Syntax.t2 = t2 }
let (tm_admit :
  Pulse_Syntax.ctag ->
    Pulse_Syntax.universe ->
      Pulse_Syntax.term ->
        Pulse_Syntax.term FStar_Pervasives_Native.option ->
          Pulse_Syntax.st_term')
  =
  fun ctag ->
    fun u ->
      fun typ ->
        fun post ->
          Pulse_Syntax.Tm_Admit
            {
              Pulse_Syntax.ctag1 = ctag;
              Pulse_Syntax.u1 = u;
              Pulse_Syntax.typ = typ;
              Pulse_Syntax.post3 = post
            }
let (tm_protect : Pulse_Syntax.st_term -> Pulse_Syntax.st_term') =
  fun t -> Pulse_Syntax.Tm_Protect { Pulse_Syntax.t = t }
let (with_range :
  Pulse_Syntax.st_term' -> Pulse_Syntax.range -> Pulse_Syntax.st_term) =
  fun t -> fun r -> { Pulse_Syntax.term1 = t; Pulse_Syntax.range = r }