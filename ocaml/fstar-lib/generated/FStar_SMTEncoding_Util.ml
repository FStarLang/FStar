open Prims
let (mkAssume :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.caption *
    Prims.string) -> FStar_SMTEncoding_Term.decl)
  =
  fun uu___ ->
    match uu___ with
    | (tm, cap, nm) ->
        let uu___1 =
          let uu___2 = FStar_SMTEncoding_Term.escape nm in
          {
            FStar_SMTEncoding_Term.assumption_term = tm;
            FStar_SMTEncoding_Term.assumption_caption = cap;
            FStar_SMTEncoding_Term.assumption_name = uu___2;
            FStar_SMTEncoding_Term.assumption_fact_ids = []
          } in
        FStar_SMTEncoding_Term.Assume uu___1
let norng :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> FStar_Compiler_Range_Type.range -> 'uuuuu1) ->
      'uuuuu -> 'uuuuu1
  = fun f -> fun x -> f x FStar_Compiler_Range_Type.dummyRange
let (mkTrue : FStar_SMTEncoding_Term.term) =
  FStar_SMTEncoding_Term.mkTrue FStar_Compiler_Range_Type.dummyRange
let (mkFalse : FStar_SMTEncoding_Term.term) =
  FStar_SMTEncoding_Term.mkFalse FStar_Compiler_Range_Type.dummyRange
let (mkInteger : Prims.string -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkInteger
let (mkInteger' : Prims.int -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkInteger'
let (mkReal : Prims.string -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkReal
let (mkBoundV : Prims.int -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkBoundV
let (mkFreeV : FStar_SMTEncoding_Term.fv -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkFreeV
let (mkApp' :
  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkApp'
let (mkApp :
  (Prims.string * FStar_SMTEncoding_Term.term Prims.list) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkApp
let (mkNot : FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkNot
let (mkMinus : FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkMinus
let (mkAnd :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkAnd
let (mkOr :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkOr
let (mkImp :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkImp
let (mkIff :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkIff
let (mkEq :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkEq
let (mkLT :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkLT
let (mkLTE :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkLTE
let (mkGT :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkGT
let (mkGTE :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkGTE
let (mkAdd :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkAdd
let (mkSub :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkSub
let (mkDiv :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkDiv
let (mkRealDiv :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkRealDiv
let (mkMul :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkMul
let (mkMod :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkMod
let (mkNatToBv :
  Prims.int -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun sz -> norng (FStar_SMTEncoding_Term.mkNatToBv sz)
let (mkBvAnd :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkBvAnd
let (mkBvXor :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkBvXor
let (mkBvOr :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkBvOr
let (mkBvAdd :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkBvAdd
let (mkBvSub :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkBvSub
let (mkBvShl :
  Prims.int ->
    (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
      FStar_SMTEncoding_Term.term)
  = fun sz -> norng (FStar_SMTEncoding_Term.mkBvShl sz)
let (mkBvShr :
  Prims.int ->
    (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
      FStar_SMTEncoding_Term.term)
  = fun sz -> norng (FStar_SMTEncoding_Term.mkBvShr sz)
let (mkBvUdiv :
  Prims.int ->
    (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
      FStar_SMTEncoding_Term.term)
  = fun sz -> norng (FStar_SMTEncoding_Term.mkBvUdiv sz)
let (mkBvMod :
  Prims.int ->
    (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
      FStar_SMTEncoding_Term.term)
  = fun sz -> norng (FStar_SMTEncoding_Term.mkBvMod sz)
let (mkBvMul :
  Prims.int ->
    (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
      FStar_SMTEncoding_Term.term)
  = fun sz -> norng (FStar_SMTEncoding_Term.mkBvMul sz)
let (mkBvUlt :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkBvUlt
let (mkBvUext :
  Prims.int -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun sz -> norng (FStar_SMTEncoding_Term.mkBvUext sz)
let (mkBvToNat : FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkBvToNat
let (mkITE :
  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term *
    FStar_SMTEncoding_Term.term) -> FStar_SMTEncoding_Term.term)
  = norng FStar_SMTEncoding_Term.mkITE
let (mkCases :
  FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mkCases
let norng2 :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu -> 'uuuuu1 -> FStar_Compiler_Range_Type.range -> 'uuuuu2) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2
  = fun f -> fun x -> fun y -> f x y FStar_Compiler_Range_Type.dummyRange
let norng3 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    ('uuuuu ->
       'uuuuu1 -> 'uuuuu2 -> FStar_Compiler_Range_Type.range -> 'uuuuu3)
      -> 'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3
  =
  fun f ->
    fun x -> fun y -> fun z -> f x y z FStar_Compiler_Range_Type.dummyRange
let norng4 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 .
    ('uuuuu ->
       'uuuuu1 ->
         'uuuuu2 -> 'uuuuu3 -> FStar_Compiler_Range_Type.range -> 'uuuuu4)
      -> 'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4
  =
  fun f ->
    fun x ->
      fun y ->
        fun z -> fun w -> f x y z w FStar_Compiler_Range_Type.dummyRange
let (mk_Term_app :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
  = norng2 FStar_SMTEncoding_Term.mk_Term_app
let (mk_Term_uvar : Prims.int -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mk_Term_uvar
let (mk_and_l :
  FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mk_and_l
let (mk_or_l :
  FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mk_or_l
let (mk_ApplyTT :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
  = norng2 FStar_SMTEncoding_Term.mk_ApplyTT
let (mk_String_const : Prims.string -> FStar_SMTEncoding_Term.term) =
  norng FStar_SMTEncoding_Term.mk_String_const
let (mk_Precedes :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
  = norng4 FStar_SMTEncoding_Term.mk_Precedes
let (is_smt_reifiable_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun en ->
    fun l ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name en l in
      (FStar_TypeChecker_Env.is_reifiable_effect en l1) &&
        (let uu___ =
           let uu___1 =
             FStar_Compiler_Effect.op_Bar_Greater l1
               (FStar_TypeChecker_Env.get_effect_decl en) in
           FStar_Compiler_Effect.op_Bar_Greater uu___1
             FStar_Syntax_Util.is_layered in
         Prims.op_Negation uu___)
let (is_smt_reifiable_comp :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun en ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_smt_reifiable_effect en ct.FStar_Syntax_Syntax.effect_name
      | uu___ -> false
let (is_smt_reifiable_rc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool)
  =
  fun en ->
    fun rc ->
      FStar_Compiler_Effect.op_Bar_Greater
        rc.FStar_Syntax_Syntax.residual_effect (is_smt_reifiable_effect en)
let (is_smt_reifiable_function :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun en ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress t in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) ->
          let uu___2 =
            FStar_Compiler_Effect.op_Bar_Greater c
              FStar_Syntax_Util.comp_effect_name in
          FStar_Compiler_Effect.op_Bar_Greater uu___2
            (is_smt_reifiable_effect en)
      | uu___1 -> false