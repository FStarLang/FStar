open Prims
let (__brs_of :
  Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.branch Prims.list) =
  fun t ->
    let uu___ = t.Pulse_Syntax_Base.term1 in
    match uu___ with
    | Pulse_Syntax_Base.Tm_Match
        { Pulse_Syntax_Base.sc = uu___1; Pulse_Syntax_Base.returns_ = uu___2;
          Pulse_Syntax_Base.brs = brs;_}
        -> brs
let (open_term_pairs' :
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index ->
        (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list)
  =
  fun t ->
    fun v ->
      fun i ->
        Pulse_Syntax_Naming.subst_term_pairs t
          [Pulse_Syntax_Naming.DT (i, v)]
let (close_term_pairs' :
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index ->
        (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list)
  =
  fun t ->
    fun v ->
      fun i ->
        Pulse_Syntax_Naming.subst_term_pairs t
          [Pulse_Syntax_Naming.ND (v, i)]