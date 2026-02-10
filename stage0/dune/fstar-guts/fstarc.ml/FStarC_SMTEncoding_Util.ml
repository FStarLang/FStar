open Prims
let mkAssume
  (uu___ :
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.caption *
      Prims.string))
  : FStarC_SMTEncoding_Term.decl=
  match uu___ with
  | (tm, cap, nm) ->
      let uu___1 =
        let uu___2 = FStarC_SMTEncoding_Term.escape nm in
        let uu___3 = FStarC_SMTEncoding_Term.free_top_level_names tm in
        {
          FStarC_SMTEncoding_Term.assumption_term = tm;
          FStarC_SMTEncoding_Term.assumption_caption = cap;
          FStarC_SMTEncoding_Term.assumption_name = uu___2;
          FStarC_SMTEncoding_Term.assumption_fact_ids = [];
          FStarC_SMTEncoding_Term.assumption_free_names = uu___3
        } in
      FStarC_SMTEncoding_Term.Assume uu___1
let norng (f : 'a -> FStarC_Range_Type.t -> FStarC_SMTEncoding_Term.term)
  (x : 'a) : FStarC_SMTEncoding_Term.term= f x FStarC_Range_Type.dummyRange
let mkTrue : FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkTrue FStarC_Range_Type.dummyRange
let mkFalse : FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkFalse FStarC_Range_Type.dummyRange
let mkInteger : Prims.string -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkInteger
let mkInteger' : Prims.int -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkInteger'
let mkReal : Prims.string -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkReal
let mkBoundV : Prims.int -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBoundV
let mkFreeV : FStarC_SMTEncoding_Term.fv -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkFreeV
let mkApp' :
  (FStarC_SMTEncoding_Term.op * FStarC_SMTEncoding_Term.term Prims.list) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkApp'
let mkApp :
  (Prims.string * FStarC_SMTEncoding_Term.term Prims.list) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkApp
let mkNot : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkNot
let mkMinus : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkMinus
let mkAnd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkAnd
let mkOr :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkOr
let mkImp :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkImp
let mkIff :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkIff
let mkEq :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkEq
let mkLT :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkLT
let mkLTE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkLTE
let mkGT :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkGT
let mkGTE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkGTE
let mkAdd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkAdd
let mkSub :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkSub
let mkDiv :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkDiv
let mkRealDiv :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkRealDiv
let mkMul :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkMul
let mkMod :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkMod
let mkNatToBv (sz : Prims.int) :
  FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkNatToBv sz)
let mkBvAnd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvAnd
let mkBvXor :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvXor
let mkBvOr :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvOr
let mkBvAdd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvAdd
let mkBvSub :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvSub
let mkBvShl (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvShl sz)
let mkBvShr (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvShr sz)
let mkBvUdiv (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvUdiv sz)
let mkBvMod (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvMod sz)
let mkBvMul (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvMul sz)
let mkBvShl' (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvShl' sz)
let mkBvShr' (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvShr' sz)
let mkBvUdivUnsafe (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvUdivUnsafe sz)
let mkBvModUnsafe (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvModUnsafe sz)
let mkBvMul' (sz : Prims.int) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvMul' sz)
let mkBvUlt :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvUlt
let mkBvUext (sz : Prims.int) :
  FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng (FStarC_SMTEncoding_Term.mkBvUext sz)
let mkBvNot : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvNot
let mkBvToNat : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkBvToNat
let mkITE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term *
    FStarC_SMTEncoding_Term.term) -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkITE
let mkCases :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mkCases
let norng2
  (f : 'a -> 'b -> FStarC_Range_Type.t -> FStarC_SMTEncoding_Term.term)
  (x : 'a) (y : 'b) : FStarC_SMTEncoding_Term.term=
  f x y FStarC_Range_Type.dummyRange
let norng3
  (f : 'a -> 'b -> 'c -> FStarC_Range_Type.t -> FStarC_SMTEncoding_Term.term)
  (x : 'a) (y : 'b) (z : 'c) : FStarC_SMTEncoding_Term.term=
  f x y z FStarC_Range_Type.dummyRange
let norng4
  (f :
    'a ->
      'b -> 'c -> 'd -> FStarC_Range_Type.t -> FStarC_SMTEncoding_Term.term)
  (x : 'a) (y : 'b) (z : 'c) (w : 'd) : FStarC_SMTEncoding_Term.term=
  f x y z w FStarC_Range_Type.dummyRange
let mk_Term_app :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng2 FStarC_SMTEncoding_Term.mk_Term_app
let mk_and_l :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mk_and_l
let mk_or_l :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mk_or_l
let mk_ApplyTT :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng2 FStarC_SMTEncoding_Term.mk_ApplyTT
let mk_String_const : Prims.string -> FStarC_SMTEncoding_Term.term=
  norng FStarC_SMTEncoding_Term.mk_String_const
let mk_Precedes (u0 : FStarC_SMTEncoding_Term.term)
  (u1 : FStarC_SMTEncoding_Term.term) :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term ->
      FStarC_SMTEncoding_Term.term ->
        FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng4 (FStarC_SMTEncoding_Term.mk_Precedes u0 u1)
let mk_LexCons :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term ->
      FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term=
  norng3 FStarC_SMTEncoding_Term.mk_LexCons
let mk_lex_t : FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_lex_t FStarC_Range_Type.dummyRange
let mk_LexTop : FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mk_LexTop FStarC_Range_Type.dummyRange
let is_smt_reifiable_effect (en : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) : Prims.bool=
  let l1 = FStarC_TypeChecker_Env.norm_eff_name en l in
  (FStarC_TypeChecker_Env.is_reifiable_effect en l1) &&
    (let uu___ =
       let uu___1 = FStarC_TypeChecker_Env.get_effect_decl en l1 in
       FStarC_Syntax_Util.is_layered uu___1 in
     Prims.op_Negation uu___)
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
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = uu___1; FStarC_Syntax_Syntax.comp = c;_}
      ->
      let uu___2 = FStarC_Syntax_Util.comp_effect_name c in
      is_smt_reifiable_effect en uu___2
  | uu___1 -> false
