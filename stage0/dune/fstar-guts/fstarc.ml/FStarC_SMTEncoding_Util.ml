open Prims
let mkAssume
  (x :
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.caption *
      Prims.string))
  : FStarC_SMTEncoding_Term.decl=
  let uu___ = x in
  match uu___ with
  | (tm, cap, nm) ->
      FStarC_SMTEncoding_Term.Assume
        {
          FStarC_SMTEncoding_Term.assumption_term = tm;
          FStarC_SMTEncoding_Term.assumption_caption = cap;
          FStarC_SMTEncoding_Term.assumption_name =
            (FStarC_SMTEncoding_Term.escape nm);
          FStarC_SMTEncoding_Term.assumption_fact_ids = []
        }
let mkTrue : FStarC_SMTEncoding_Term.term= FStarC_SMTEncoding_Term.mkTrue
let mkFalse : FStarC_SMTEncoding_Term.term= FStarC_SMTEncoding_Term.mkFalse
let mkInteger : Prims.string -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkInteger
let mkInteger' : Prims.int -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkInteger'
let mkReal : Prims.string -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkReal
let mkBoundV : Prims.int -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBoundV
let mkFreeV : FStarC_SMTEncoding_Term.fv -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkFreeV
let mkApp' :
  (FStarC_SMTEncoding_Term.op * FStarC_SMTEncoding_Term.term Prims.list) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkApp'
let mkApp :
  (Prims.string * FStarC_SMTEncoding_Term.term Prims.list) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkApp
let mkNot : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkNot
let mkMinus : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkMinus
let mkAnd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkAnd
let mkOr :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkOr
let mkImp :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkImp
let mkIff :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkIff
let mkEq :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkEq
let mkLT :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkLT
let mkLTE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkLTE
let mkGT :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkGT
let mkGTE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkGTE
let mkAdd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkAdd
let mkSub :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkSub
let mkDiv :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkDiv
let mkRealDiv :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkRealDiv
let mkMul :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkMul
let mkMod :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkMod
let mkNatToBv :
  Prims.int -> FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkNatToBv
let mkBvAnd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvAnd
let mkBvXor :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvXor
let mkBvOr :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvOr
let mkBvAdd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvAdd
let mkBvSub :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvSub
let mkBvShl :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvShl
let mkBvShr :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvShr
let mkBvRol :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvRol
let mkBvRor :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvRor
let mkBvUdiv :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvUdiv
let mkBvMod :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvMod
let mkBvMul :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvMul
let mkBvShl' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvShl'
let mkBvShr' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvShr'
let mkBvRol' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvRol'
let mkBvRor' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvRor'
let mkBvUdivUnsafe :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvUdivUnsafe
let mkBvModUnsafe :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvModUnsafe
let mkBvMul' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvMul'
let mkBvUlt :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvUlt
let mkBvUext :
  Prims.int -> FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvUext
let mkBvNot : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvNot
let mkBvToNat : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkBvToNat
let mkITE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term *
    FStarC_SMTEncoding_Term.term) -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkITE
let mkCases :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkCases
let mk_Term_app :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_Term_app
let mk_and_l :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_and_l
let mk_or_l :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_or_l
let mk_ApplyTT :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_ApplyTT
let mk_String_const : Prims.string -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_String_const
let mk_Precedes :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term ->
      FStarC_SMTEncoding_Term.term ->
        FStarC_SMTEncoding_Term.term ->
          FStarC_SMTEncoding_Term.term ->
            FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_Precedes
let mk_LexCons :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term ->
      FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_LexCons
let mk_lex_t : FStarC_SMTEncoding_Term.term= FStarC_SMTEncoding_Term.mk_lex_t
let mk_LexTop : FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_LexTop
let is_smt_reifiable_effect (en : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) : Prims.bool=
  let l1 = FStarC_TypeChecker_Env.norm_eff_name en l in
  FStarC_TypeChecker_Env.is_reifiable_effect en l1
let is_smt_reifiable_comp (en : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : Prims.bool=
  match c.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Comp ct ->
      is_smt_reifiable_effect en ct.FStarC_Syntax_Syntax.effect_name
  | uu___ -> false
let is_smt_reifiable_rc (en : FStarC_TypeChecker_Env.env)
  (rc : FStarC_Syntax_Syntax.residual_comp) : Prims.bool=
  is_smt_reifiable_effect en rc.FStarC_Syntax_Syntax.residual_effect
let is_smt_reifiable_function (en : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_arrow uu___1 ->
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Syntax_Util.arrow_node_formals_comp_ln t in
          FStar_Pervasives_Native.snd uu___4 in
        FStarC_Syntax_Util.comp_effect_name uu___3 in
      is_smt_reifiable_effect en uu___2
  | uu___1 -> false
