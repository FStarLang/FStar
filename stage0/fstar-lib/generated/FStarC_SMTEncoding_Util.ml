open Prims
let (mkAssume :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.caption *
    Prims.string) -> FStarC_SMTEncoding_Term.decl)
  =
  fun uu___ ->
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
let norng :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> FStarC_Compiler_Range_Type.range -> 'uuuuu1) ->
      'uuuuu -> 'uuuuu1
  = fun f -> fun x -> f x FStarC_Compiler_Range_Type.dummyRange
let (mkTrue : FStarC_SMTEncoding_Term.term) =
  FStarC_SMTEncoding_Term.mkTrue FStarC_Compiler_Range_Type.dummyRange
let (mkFalse : FStarC_SMTEncoding_Term.term) =
  FStarC_SMTEncoding_Term.mkFalse FStarC_Compiler_Range_Type.dummyRange
let (mkInteger : Prims.string -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkInteger
let (mkInteger' : Prims.int -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkInteger'
let (mkReal : Prims.string -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkReal
let (mkBoundV : Prims.int -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkBoundV
let (mkFreeV : FStarC_SMTEncoding_Term.fv -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkFreeV
let (mkApp' :
  (FStarC_SMTEncoding_Term.op * FStarC_SMTEncoding_Term.term Prims.list) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkApp'
let (mkApp :
  (Prims.string * FStarC_SMTEncoding_Term.term Prims.list) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkApp
let (mkNot : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkNot
let (mkMinus : FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkMinus
let (mkAnd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkAnd
let (mkOr :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkOr
let (mkImp :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkImp
let (mkIff :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkIff
let (mkEq :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkEq
let (mkLT :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkLT
let (mkLTE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkLTE
let (mkGT :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkGT
let (mkGTE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkGTE
let (mkAdd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkAdd
let (mkSub :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkSub
let (mkDiv :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkDiv
let (mkRealDiv :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkRealDiv
let (mkMul :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkMul
let (mkMod :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkMod
let (mkNatToBv :
  Prims.int -> FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkNatToBv sz)
let (mkBvAnd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkBvAnd
let (mkBvXor :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkBvXor
let (mkBvOr :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkBvOr
let (mkBvAdd :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkBvAdd
let (mkBvSub :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkBvSub
let (mkBvShl :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvShl sz)
let (mkBvShr :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvShr sz)
let (mkBvUdiv :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvUdiv sz)
let (mkBvMod :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvMod sz)
let (mkBvMul :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvMul sz)
let (mkBvShl' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvShl' sz)
let (mkBvShr' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvShr' sz)
let (mkBvUdivUnsafe :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvUdivUnsafe sz)
let (mkBvModUnsafe :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvModUnsafe sz)
let (mkBvMul' :
  Prims.int ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
      FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvMul' sz)
let (mkBvUlt :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkBvUlt
let (mkBvUext :
  Prims.int -> FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term)
  = fun sz -> norng (FStarC_SMTEncoding_Term.mkBvUext sz)
let (mkBvToNat :
  FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkBvToNat
let (mkITE :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term *
    FStarC_SMTEncoding_Term.term) -> FStarC_SMTEncoding_Term.term)
  = norng FStarC_SMTEncoding_Term.mkITE
let (mkCases :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mkCases
let norng2 :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu -> 'uuuuu1 -> FStarC_Compiler_Range_Type.range -> 'uuuuu2) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2
  = fun f -> fun x -> fun y -> f x y FStarC_Compiler_Range_Type.dummyRange
let norng3 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    ('uuuuu ->
       'uuuuu1 -> 'uuuuu2 -> FStarC_Compiler_Range_Type.range -> 'uuuuu3)
      -> 'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3
  =
  fun f ->
    fun x -> fun y -> fun z -> f x y z FStarC_Compiler_Range_Type.dummyRange
let norng4 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 .
    ('uuuuu ->
       'uuuuu1 ->
         'uuuuu2 -> 'uuuuu3 -> FStarC_Compiler_Range_Type.range -> 'uuuuu4)
      -> 'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4
  =
  fun f ->
    fun x ->
      fun y ->
        fun z -> fun w -> f x y z w FStarC_Compiler_Range_Type.dummyRange
let (mk_Term_app :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term)
  = norng2 FStarC_SMTEncoding_Term.mk_Term_app
let (mk_Term_uvar : Prims.int -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mk_Term_uvar
let (mk_and_l :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mk_and_l
let (mk_or_l :
  FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mk_or_l
let (mk_ApplyTT :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term)
  = norng2 FStarC_SMTEncoding_Term.mk_ApplyTT
let (mk_String_const : Prims.string -> FStarC_SMTEncoding_Term.term) =
  norng FStarC_SMTEncoding_Term.mk_String_const
let (mk_Precedes :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term ->
      FStarC_SMTEncoding_Term.term ->
        FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term)
  = norng4 FStarC_SMTEncoding_Term.mk_Precedes
let (is_smt_reifiable_effect :
  FStarC_TypeChecker_Env.env -> FStarC_Ident.lident -> Prims.bool) =
  fun en ->
    fun l ->
      let l1 = FStarC_TypeChecker_Env.norm_eff_name en l in
      (FStarC_TypeChecker_Env.is_reifiable_effect en l1) &&
        (let uu___ =
           let uu___1 = FStarC_TypeChecker_Env.get_effect_decl en l1 in
           FStarC_Syntax_Util.is_layered uu___1 in
         Prims.op_Negation uu___)
let (is_smt_reifiable_comp :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.comp -> Prims.bool) =
  fun en ->
    fun c ->
      match c.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Comp ct ->
          is_smt_reifiable_effect en ct.FStarC_Syntax_Syntax.effect_name
      | uu___ -> false
let (is_smt_reifiable_rc :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.residual_comp -> Prims.bool)
  =
  fun en ->
    fun rc ->
      is_smt_reifiable_effect en rc.FStarC_Syntax_Syntax.residual_effect
let (is_smt_reifiable_function :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun en ->
    fun t ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_arrow
          { FStarC_Syntax_Syntax.bs1 = uu___1;
            FStarC_Syntax_Syntax.comp = c;_}
          ->
          is_smt_reifiable_effect en (FStarC_Syntax_Util.comp_effect_name c)
      | uu___1 -> false