open Prims
let (eq_ident : FStarC_Ident.ident -> FStarC_Ident.ident -> Prims.bool) =
  fun i1 -> fun i2 -> FStarC_Ident.ident_equals i1 i2
let eq_list :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun f ->
    fun t1 ->
      fun t2 ->
        ((FStarC_Compiler_List.length t1) = (FStarC_Compiler_List.length t2))
          && (FStarC_Compiler_List.forall2 f t1 t2)
let eq_option :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun f ->
    fun t1 ->
      fun t2 ->
        match (t1, t2) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (FStar_Pervasives_Native.Some t11, FStar_Pervasives_Native.Some
           t21) -> f t11 t21
        | uu___ -> false
let (eq_sconst : FStarC_Const.sconst -> FStarC_Const.sconst -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (FStarC_Const.Const_effect, FStarC_Const.Const_effect) -> true
      | (FStarC_Const.Const_unit, FStarC_Const.Const_unit) -> true
      | (FStarC_Const.Const_bool b1, FStarC_Const.Const_bool b2) -> b1 = b2
      | (FStarC_Const.Const_int (s1, sw1), FStarC_Const.Const_int (s2, sw2))
          -> (s1 = s2) && (sw1 = sw2)
      | (FStarC_Const.Const_char c11, FStarC_Const.Const_char c21) ->
          c11 = c21
      | (FStarC_Const.Const_string (s1, uu___), FStarC_Const.Const_string
         (s2, uu___1)) -> s1 = s2
      | (FStarC_Const.Const_real s1, FStarC_Const.Const_real s2) -> s1 = s2
      | (FStarC_Const.Const_range r1, FStarC_Const.Const_range r2) -> r1 = r2
      | (FStarC_Const.Const_reify uu___, FStarC_Const.Const_reify uu___1) ->
          true
      | (FStarC_Const.Const_reflect l1, FStarC_Const.Const_reflect l2) ->
          FStarC_Ident.lid_equals l1 l2
      | uu___ -> false
let rec (eq_term :
  FStarC_Parser_AST.term -> FStarC_Parser_AST.term -> Prims.bool) =
  fun t1 ->
    fun t2 -> eq_term' t1.FStarC_Parser_AST.tm t2.FStarC_Parser_AST.tm
and (eq_terms :
  FStarC_Parser_AST.term Prims.list ->
    FStarC_Parser_AST.term Prims.list -> Prims.bool)
  = fun t1 -> fun t2 -> eq_list eq_term t1 t2
and (eq_arg :
  (FStarC_Parser_AST.term * FStarC_Parser_AST.imp) ->
    (FStarC_Parser_AST.term * FStarC_Parser_AST.imp) -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = t1 in
      match uu___ with
      | (t11, a1) ->
          let uu___1 = t2 in
          (match uu___1 with
           | (t21, a2) -> (eq_term t11 t21) && (eq_imp a1 a2))
and (eq_imp : FStarC_Parser_AST.imp -> FStarC_Parser_AST.imp -> Prims.bool) =
  fun i1 ->
    fun i2 ->
      match (i1, i2) with
      | (FStarC_Parser_AST.FsTypApp, FStarC_Parser_AST.FsTypApp) -> true
      | (FStarC_Parser_AST.Hash, FStarC_Parser_AST.Hash) -> true
      | (FStarC_Parser_AST.UnivApp, FStarC_Parser_AST.UnivApp) -> true
      | (FStarC_Parser_AST.Infix, FStarC_Parser_AST.Infix) -> true
      | (FStarC_Parser_AST.Nothing, FStarC_Parser_AST.Nothing) -> true
      | (FStarC_Parser_AST.HashBrace t1, FStarC_Parser_AST.HashBrace t2) ->
          eq_term t1 t2
      | uu___ -> false
and (eq_args :
  (FStarC_Parser_AST.term * FStarC_Parser_AST.imp) Prims.list ->
    (FStarC_Parser_AST.term * FStarC_Parser_AST.imp) Prims.list -> Prims.bool)
  = fun t1 -> fun t2 -> eq_list eq_arg t1 t2
and (eq_arg_qualifier :
  FStarC_Parser_AST.arg_qualifier ->
    FStarC_Parser_AST.arg_qualifier -> Prims.bool)
  =
  fun arg_qualifier1 ->
    fun arg_qualifier2 ->
      match (arg_qualifier1, arg_qualifier2) with
      | (FStarC_Parser_AST.Implicit, FStarC_Parser_AST.Implicit) -> true
      | (FStarC_Parser_AST.Equality, FStarC_Parser_AST.Equality) -> true
      | (FStarC_Parser_AST.Meta t1, FStarC_Parser_AST.Meta t2) ->
          eq_term t1 t2
      | (FStarC_Parser_AST.TypeClassArg, FStarC_Parser_AST.TypeClassArg) ->
          true
      | uu___ -> false
and (eq_pattern :
  FStarC_Parser_AST.pattern -> FStarC_Parser_AST.pattern -> Prims.bool) =
  fun p1 ->
    fun p2 -> eq_pattern' p1.FStarC_Parser_AST.pat p2.FStarC_Parser_AST.pat
and (eq_aqual :
  FStarC_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStarC_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.bool)
  = fun a1 -> fun a2 -> eq_option eq_arg_qualifier a1 a2
and (eq_pattern' :
  FStarC_Parser_AST.pattern' -> FStarC_Parser_AST.pattern' -> Prims.bool) =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStarC_Parser_AST.PatWild (q1, a1), FStarC_Parser_AST.PatWild
         (q2, a2)) -> (eq_aqual q1 q2) && (eq_terms a1 a2)
      | (FStarC_Parser_AST.PatConst s1, FStarC_Parser_AST.PatConst s2) ->
          eq_sconst s1 s2
      | (FStarC_Parser_AST.PatApp (p11, ps1), FStarC_Parser_AST.PatApp
         (p21, ps2)) -> (eq_pattern p11 p21) && (eq_list eq_pattern ps1 ps2)
      | (FStarC_Parser_AST.PatTvar (i1, aq1, as1), FStarC_Parser_AST.PatTvar
         (i2, aq2, as2)) ->
          ((FStarC_Ident.ident_equals i1 i2) && (eq_aqual aq1 aq2)) &&
            (eq_terms as1 as2)
      | (FStarC_Parser_AST.PatVar (i1, aq1, as1), FStarC_Parser_AST.PatVar
         (i2, aq2, as2)) ->
          ((FStarC_Ident.ident_equals i1 i2) && (eq_aqual aq1 aq2)) &&
            (eq_terms as1 as2)
      | (FStarC_Parser_AST.PatName l1, FStarC_Parser_AST.PatName l2) ->
          FStarC_Ident.lid_equals l1 l2
      | (FStarC_Parser_AST.PatOr ps1, FStarC_Parser_AST.PatOr ps2) ->
          eq_list eq_pattern ps1 ps2
      | (FStarC_Parser_AST.PatList ps1, FStarC_Parser_AST.PatList ps2) ->
          eq_list eq_pattern ps1 ps2
      | (FStarC_Parser_AST.PatTuple (ps1, b1), FStarC_Parser_AST.PatTuple
         (ps2, b2)) -> (eq_list eq_pattern ps1 ps2) && (b1 = b2)
      | (FStarC_Parser_AST.PatRecord ps1, FStarC_Parser_AST.PatRecord ps2) ->
          eq_list
            (fun uu___ ->
               fun uu___1 ->
                 match (uu___, uu___1) with
                 | ((l1, p11), (l2, p21)) ->
                     (FStarC_Ident.lid_equals l1 l2) && (eq_pattern p11 p21))
            ps1 ps2
      | (FStarC_Parser_AST.PatAscribed (p11, (t1, topt1)),
         FStarC_Parser_AST.PatAscribed (p21, (t2, topt2))) ->
          ((eq_pattern p11 p21) && (eq_term t1 t2)) &&
            (eq_option eq_term topt1 topt2)
      | (FStarC_Parser_AST.PatOp i1, FStarC_Parser_AST.PatOp i2) ->
          eq_ident i1 i2
      | (FStarC_Parser_AST.PatVQuote t1, FStarC_Parser_AST.PatVQuote t2) ->
          eq_term t1 t2
      | uu___ -> false
and (eq_term' :
  FStarC_Parser_AST.term' -> FStarC_Parser_AST.term' -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (FStarC_Parser_AST.Wild, FStarC_Parser_AST.Wild) -> true
      | (FStarC_Parser_AST.Const s1, FStarC_Parser_AST.Const s2) ->
          FStarC_Const.eq_const s1 s2
      | (FStarC_Parser_AST.Op (i1, ts1), FStarC_Parser_AST.Op (i2, ts2)) ->
          (eq_ident i1 i2) && (eq_terms ts1 ts2)
      | (FStarC_Parser_AST.Tvar i1, FStarC_Parser_AST.Tvar i2) ->
          eq_ident i1 i2
      | (FStarC_Parser_AST.Uvar i1, FStarC_Parser_AST.Uvar i2) ->
          eq_ident i1 i2
      | (FStarC_Parser_AST.Var l1, FStarC_Parser_AST.Var l2) ->
          FStarC_Ident.lid_equals l1 l2
      | (FStarC_Parser_AST.Name l1, FStarC_Parser_AST.Name l2) ->
          FStarC_Ident.lid_equals l1 l2
      | (FStarC_Parser_AST.Projector (l1, i1), FStarC_Parser_AST.Projector
         (l2, i2)) ->
          (FStarC_Ident.lid_equals l1 l2) &&
            (FStarC_Ident.ident_equals i1 i2)
      | (FStarC_Parser_AST.Construct (l1, args1), FStarC_Parser_AST.Construct
         (l2, args2)) ->
          (FStarC_Ident.lid_equals l1 l2) && (eq_args args1 args2)
      | (FStarC_Parser_AST.Function (brs1, _r1), FStarC_Parser_AST.Function
         (brs2, _r2)) -> eq_list eq_branch brs1 brs2
      | (FStarC_Parser_AST.Abs (ps1, t11), FStarC_Parser_AST.Abs (ps2, t21))
          -> (eq_list eq_pattern ps1 ps2) && (eq_term t11 t21)
      | (FStarC_Parser_AST.App (h1, t11, i1), FStarC_Parser_AST.App
         (h2, t21, i2)) ->
          ((eq_term h1 h2) && (eq_term t11 t21)) && (eq_imp i1 i2)
      | (FStarC_Parser_AST.Let (lq1, defs1, t11), FStarC_Parser_AST.Let
         (lq2, defs2, t21)) ->
          ((lq1 = lq2) &&
             (eq_list
                (fun uu___ ->
                   fun uu___1 ->
                     match (uu___, uu___1) with
                     | ((o1, (p1, t12)), (o2, (p2, t22))) ->
                         ((eq_option eq_terms o1 o2) && (eq_pattern p1 p2))
                           && (eq_term t12 t22)) defs1 defs2))
            && (eq_term t11 t21)
      | (FStarC_Parser_AST.LetOperator (defs1, t11),
         FStarC_Parser_AST.LetOperator (defs2, t21)) ->
          (eq_list
             (fun uu___ ->
                fun uu___1 ->
                  match (uu___, uu___1) with
                  | ((i1, ps1, t12), (i2, ps2, t22)) ->
                      ((eq_ident i1 i2) && (eq_pattern ps1 ps2)) &&
                        (eq_term t12 t22)) defs1 defs2)
            && (eq_term t11 t21)
      | (FStarC_Parser_AST.LetOpen (l1, t11), FStarC_Parser_AST.LetOpen
         (l2, t21)) -> (FStarC_Ident.lid_equals l1 l2) && (eq_term t11 t21)
      | (FStarC_Parser_AST.LetOpenRecord (t11, t21, t3),
         FStarC_Parser_AST.LetOpenRecord (t4, t5, t6)) ->
          ((eq_term t11 t4) && (eq_term t21 t5)) && (eq_term t3 t6)
      | (FStarC_Parser_AST.Seq (t11, t21), FStarC_Parser_AST.Seq (t3, t4)) ->
          (eq_term t11 t3) && (eq_term t21 t4)
      | (FStarC_Parser_AST.Bind (i1, t11, t21), FStarC_Parser_AST.Bind
         (i2, t3, t4)) ->
          ((FStarC_Ident.ident_equals i1 i2) && (eq_term t11 t3)) &&
            (eq_term t21 t4)
      | (FStarC_Parser_AST.If (t11, i1, mra1, t21, t3), FStarC_Parser_AST.If
         (t4, i2, mra2, t5, t6)) ->
          ((((eq_term t11 t4) && (eq_option eq_ident i1 i2)) &&
              (eq_option eq_match_returns_annotation mra1 mra2))
             && (eq_term t21 t5))
            && (eq_term t3 t6)
      | (FStarC_Parser_AST.Match (t11, i1, mra1, bs1),
         FStarC_Parser_AST.Match (t21, i2, mra2, bs2)) ->
          (((eq_term t11 t21) && (eq_option eq_ident i1 i2)) &&
             (eq_option eq_match_returns_annotation mra1 mra2))
            && (eq_list eq_branch bs1 bs2)
      | (FStarC_Parser_AST.TryWith (t11, bs1), FStarC_Parser_AST.TryWith
         (t21, bs2)) -> (eq_term t11 t21) && (eq_list eq_branch bs1 bs2)
      | (FStarC_Parser_AST.Ascribed (t11, t21, topt1, b1),
         FStarC_Parser_AST.Ascribed (t3, t4, topt2, b2)) ->
          (((eq_term t11 t3) && (eq_term t21 t4)) &&
             (eq_option eq_term topt1 topt2))
            && (b1 = b2)
      | (FStarC_Parser_AST.Record (topt1, fs1), FStarC_Parser_AST.Record
         (topt2, fs2)) ->
          (eq_option eq_term topt1 topt2) &&
            (eq_list
               (fun uu___ ->
                  fun uu___1 ->
                    match (uu___, uu___1) with
                    | ((l1, t11), (l2, t21)) ->
                        (FStarC_Ident.lid_equals l1 l2) && (eq_term t11 t21))
               fs1 fs2)
      | (FStarC_Parser_AST.Project (t11, l1), FStarC_Parser_AST.Project
         (t21, l2)) -> (eq_term t11 t21) && (FStarC_Ident.lid_equals l1 l2)
      | (FStarC_Parser_AST.Product (bs1, t11), FStarC_Parser_AST.Product
         (bs2, t21)) -> (eq_list eq_binder bs1 bs2) && (eq_term t11 t21)
      | (FStarC_Parser_AST.Sum (bs1, t11), FStarC_Parser_AST.Sum (bs2, t21))
          ->
          (eq_list
             (fun b1 ->
                fun b2 ->
                  match (b1, b2) with
                  | (FStar_Pervasives.Inl b11, FStar_Pervasives.Inl b21) ->
                      eq_binder b11 b21
                  | (FStar_Pervasives.Inr t12, FStar_Pervasives.Inr t22) ->
                      eq_term t12 t22
                  | (FStar_Pervasives.Inl uu___, FStar_Pervasives.Inr uu___1)
                      -> false
                  | (FStar_Pervasives.Inr uu___, FStar_Pervasives.Inl uu___1)
                      -> false) bs1 bs2)
            && (eq_term t11 t21)
      | (FStarC_Parser_AST.QForall (bs1, ps1, t11), FStarC_Parser_AST.QForall
         (bs2, ps2, t21)) ->
          let eq_ps uu___ uu___1 =
            match (uu___, uu___1) with
            | ((is1, ts1), (is2, ts2)) ->
                (eq_list eq_ident is1 is2) &&
                  (eq_list (eq_list eq_term) ts1 ts2) in
          ((eq_list eq_binder bs1 bs2) && (eq_ps ps1 ps2)) &&
            (eq_term t11 t21)
      | (FStarC_Parser_AST.QExists (bs1, ps1, t11), FStarC_Parser_AST.QExists
         (bs2, ps2, t21)) ->
          let eq_ps uu___ uu___1 =
            match (uu___, uu___1) with
            | ((is1, ts1), (is2, ts2)) ->
                (eq_list eq_ident is1 is2) &&
                  (eq_list (eq_list eq_term) ts1 ts2) in
          ((eq_list eq_binder bs1 bs2) && (eq_ps ps1 ps2)) &&
            (eq_term t11 t21)
      | (FStarC_Parser_AST.QuantOp (i1, bs1, ps1, t11),
         FStarC_Parser_AST.QuantOp (i2, bs2, ps2, t21)) ->
          let eq_ps uu___ uu___1 =
            match (uu___, uu___1) with
            | ((is1, ts1), (is2, ts2)) ->
                (eq_list eq_ident is1 is2) &&
                  (eq_list (eq_list eq_term) ts1 ts2) in
          (((FStarC_Ident.ident_equals i1 i2) && (eq_list eq_binder bs1 bs2))
             && (eq_ps ps1 ps2))
            && (eq_term t11 t21)
      | (FStarC_Parser_AST.Refine (t11, t21), FStarC_Parser_AST.Refine
         (t3, t4)) -> (eq_binder t11 t3) && (eq_term t21 t4)
      | (FStarC_Parser_AST.NamedTyp (i1, t11), FStarC_Parser_AST.NamedTyp
         (i2, t21)) -> (eq_ident i1 i2) && (eq_term t11 t21)
      | (FStarC_Parser_AST.Paren t11, FStarC_Parser_AST.Paren t21) ->
          eq_term t11 t21
      | (FStarC_Parser_AST.Requires (t11, s1), FStarC_Parser_AST.Requires
         (t21, s2)) -> (eq_term t11 t21) && (eq_option (=) s1 s2)
      | (FStarC_Parser_AST.Ensures (t11, s1), FStarC_Parser_AST.Ensures
         (t21, s2)) -> (eq_term t11 t21) && (eq_option (=) s1 s2)
      | (FStarC_Parser_AST.LexList ts1, FStarC_Parser_AST.LexList ts2) ->
          eq_list eq_term ts1 ts2
      | (FStarC_Parser_AST.WFOrder (t11, t21), FStarC_Parser_AST.WFOrder
         (t3, t4)) -> (eq_term t11 t3) && (eq_term t21 t4)
      | (FStarC_Parser_AST.Decreases (t11, s1), FStarC_Parser_AST.Decreases
         (t21, s2)) -> (eq_term t11 t21) && (eq_option (=) s1 s2)
      | (FStarC_Parser_AST.Labeled (t11, s1, b1), FStarC_Parser_AST.Labeled
         (t21, s2, b2)) -> ((eq_term t11 t21) && (s1 = s2)) && (b1 = b2)
      | (FStarC_Parser_AST.Discrim l1, FStarC_Parser_AST.Discrim l2) ->
          FStarC_Ident.lid_equals l1 l2
      | (FStarC_Parser_AST.Attributes ts1, FStarC_Parser_AST.Attributes ts2)
          -> eq_list eq_term ts1 ts2
      | (FStarC_Parser_AST.Antiquote t11, FStarC_Parser_AST.Antiquote t21) ->
          eq_term t11 t21
      | (FStarC_Parser_AST.Quote (t11, k1), FStarC_Parser_AST.Quote
         (t21, k2)) -> (eq_term t11 t21) && (k1 = k2)
      | (FStarC_Parser_AST.VQuote t11, FStarC_Parser_AST.VQuote t21) ->
          eq_term t11 t21
      | (FStarC_Parser_AST.CalcProof (t11, t21, cs1),
         FStarC_Parser_AST.CalcProof (t3, t4, cs2)) ->
          ((eq_term t11 t3) && (eq_term t21 t4)) &&
            (eq_list eq_calc_step cs1 cs2)
      | (FStarC_Parser_AST.IntroForall (bs1, t11, t21),
         FStarC_Parser_AST.IntroForall (bs2, t3, t4)) ->
          ((eq_list eq_binder bs1 bs2) && (eq_term t11 t3)) &&
            (eq_term t21 t4)
      | (FStarC_Parser_AST.IntroExists (bs1, t11, ts1, t21),
         FStarC_Parser_AST.IntroExists (bs2, t3, ts2, t4)) ->
          (((eq_list eq_binder bs1 bs2) && (eq_term t11 t3)) &&
             (eq_list eq_term ts1 ts2))
            && (eq_term t21 t4)
      | (FStarC_Parser_AST.IntroImplies (t11, t21, b1, t3),
         FStarC_Parser_AST.IntroImplies (t4, t5, b2, t6)) ->
          (((eq_term t11 t4) && (eq_term t21 t5)) && (eq_binder b1 b2)) &&
            (eq_term t3 t6)
      | (FStarC_Parser_AST.IntroOr (b1, t11, t21, t3),
         FStarC_Parser_AST.IntroOr (b2, t4, t5, t6)) ->
          (((b1 = b2) && (eq_term t11 t4)) && (eq_term t21 t5)) &&
            (eq_term t3 t6)
      | (FStarC_Parser_AST.IntroAnd (t11, t21, t3, t4),
         FStarC_Parser_AST.IntroAnd (t5, t6, t7, t8)) ->
          (((eq_term t11 t5) && (eq_term t21 t6)) && (eq_term t3 t7)) &&
            (eq_term t4 t8)
      | (FStarC_Parser_AST.ElimForall (bs1, t11, ts1),
         FStarC_Parser_AST.ElimForall (bs2, t21, ts2)) ->
          ((eq_list eq_binder bs1 bs2) && (eq_term t11 t21)) &&
            (eq_list eq_term ts1 ts2)
      | (FStarC_Parser_AST.ElimExists (bs1, t11, t21, b1, t3),
         FStarC_Parser_AST.ElimExists (bs2, t4, t5, b2, t6)) ->
          ((((eq_list eq_binder bs1 bs2) && (eq_term t11 t4)) &&
              (eq_term t21 t5))
             && (eq_binder b1 b2))
            && (eq_term t3 t6)
      | (FStarC_Parser_AST.ElimImplies (t11, t21, t3),
         FStarC_Parser_AST.ElimImplies (t4, t5, t6)) ->
          ((eq_term t11 t4) && (eq_term t21 t5)) && (eq_term t3 t6)
      | (FStarC_Parser_AST.ElimOr (t11, t21, t3, b1, t4, b2, t5),
         FStarC_Parser_AST.ElimOr (t6, t7, t8, b3, t9, b4, t10)) ->
          ((((((eq_term t11 t6) && (eq_term t21 t7)) && (eq_term t3 t8)) &&
               (eq_binder b1 b3))
              && (eq_term t4 t9))
             && (eq_binder b2 b4))
            && (eq_term t5 t10)
      | (FStarC_Parser_AST.ElimAnd (t11, t21, t3, b1, b2, t4),
         FStarC_Parser_AST.ElimAnd (t5, t6, t7, b3, b4, t8)) ->
          (((((eq_term t11 t5) && (eq_term t21 t6)) && (eq_term t3 t7)) &&
              (eq_binder b1 b3))
             && (eq_binder b2 b4))
            && (eq_term t4 t8)
      | (FStarC_Parser_AST.ListLiteral ts1, FStarC_Parser_AST.ListLiteral
         ts2) -> eq_list eq_term ts1 ts2
      | (FStarC_Parser_AST.SeqLiteral ts1, FStarC_Parser_AST.SeqLiteral ts2)
          -> eq_list eq_term ts1 ts2
      | uu___ -> false
and (eq_calc_step :
  FStarC_Parser_AST.calc_step -> FStarC_Parser_AST.calc_step -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | (FStarC_Parser_AST.CalcStep (t1, t2, t3), FStarC_Parser_AST.CalcStep
         (t4, t5, t6)) ->
          ((eq_term t1 t4) && (eq_term t2 t5)) && (eq_term t3 t6)
and (eq_binder :
  FStarC_Parser_AST.binder -> FStarC_Parser_AST.binder -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      ((eq_binder' b1.FStarC_Parser_AST.b b2.FStarC_Parser_AST.b) &&
         (eq_aqual b1.FStarC_Parser_AST.aqual b2.FStarC_Parser_AST.aqual))
        &&
        (eq_list eq_term b1.FStarC_Parser_AST.battributes
           b2.FStarC_Parser_AST.battributes)
and (eq_binder' :
  FStarC_Parser_AST.binder' -> FStarC_Parser_AST.binder' -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (FStarC_Parser_AST.Variable i1, FStarC_Parser_AST.Variable i2) ->
          eq_ident i1 i2
      | (FStarC_Parser_AST.TVariable i1, FStarC_Parser_AST.TVariable i2) ->
          eq_ident i1 i2
      | (FStarC_Parser_AST.Annotated (i1, t1), FStarC_Parser_AST.Annotated
         (i2, t2)) -> (eq_ident i1 i2) && (eq_term t1 t2)
      | (FStarC_Parser_AST.TAnnotated (i1, t1), FStarC_Parser_AST.TAnnotated
         (i2, t2)) -> (eq_ident i1 i2) && (eq_term t1 t2)
      | (FStarC_Parser_AST.NoName t1, FStarC_Parser_AST.NoName t2) ->
          eq_term t1 t2
      | uu___ -> false
and (eq_match_returns_annotation :
  (FStarC_Ident.ident FStar_Pervasives_Native.option * FStarC_Parser_AST.term
    * Prims.bool) ->
    (FStarC_Ident.ident FStar_Pervasives_Native.option *
      FStarC_Parser_AST.term * Prims.bool) -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((i1, t1, b1), (i2, t2, b2)) ->
          ((eq_option eq_ident i1 i2) && (eq_term t1 t2)) && (b1 = b2)
and (eq_branch :
  (FStarC_Parser_AST.pattern * FStarC_Parser_AST.term
    FStar_Pervasives_Native.option * FStarC_Parser_AST.term) ->
    (FStarC_Parser_AST.pattern * FStarC_Parser_AST.term
      FStar_Pervasives_Native.option * FStarC_Parser_AST.term) -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((p1, o1, t1), (p2, o2, t2)) ->
          ((eq_pattern p1 p2) && (eq_option eq_term o1 o2)) &&
            (eq_term t1 t2)
let (eq_tycon_record :
  FStarC_Parser_AST.tycon_record ->
    FStarC_Parser_AST.tycon_record -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      eq_list
        (fun uu___ ->
           fun uu___1 ->
             match (uu___, uu___1) with
             | ((i1, a1, a2, t11), (i2, a3, a4, t21)) ->
                 (((eq_ident i1 i2) && (eq_aqual a1 a3)) &&
                    (eq_list eq_term a2 a4))
                   && (eq_term t11 t21)) t1 t2
let (eq_constructor_payload :
  FStarC_Parser_AST.constructor_payload ->
    FStarC_Parser_AST.constructor_payload -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (FStarC_Parser_AST.VpOfNotation t11, FStarC_Parser_AST.VpOfNotation
         t21) -> eq_term t11 t21
      | (FStarC_Parser_AST.VpArbitrary t11, FStarC_Parser_AST.VpArbitrary
         t21) -> eq_term t11 t21
      | (FStarC_Parser_AST.VpRecord (r1, k1), FStarC_Parser_AST.VpRecord
         (r2, k2)) -> (eq_tycon_record r1 r2) && (eq_option eq_term k1 k2)
      | uu___ -> false
let (eq_tycon :
  FStarC_Parser_AST.tycon -> FStarC_Parser_AST.tycon -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (FStarC_Parser_AST.TyconAbstract (i1, bs1, k1),
         FStarC_Parser_AST.TyconAbstract (i2, bs2, k2)) ->
          ((eq_ident i1 i2) && (eq_list eq_binder bs1 bs2)) &&
            (eq_option eq_term k1 k2)
      | (FStarC_Parser_AST.TyconAbbrev (i1, bs1, k1, t11),
         FStarC_Parser_AST.TyconAbbrev (i2, bs2, k2, t21)) ->
          (((eq_ident i1 i2) && (eq_list eq_binder bs1 bs2)) &&
             (eq_option eq_term k1 k2))
            && (eq_term t11 t21)
      | (FStarC_Parser_AST.TyconRecord (i1, bs1, k1, a1, r1),
         FStarC_Parser_AST.TyconRecord (i2, bs2, k2, a2, r2)) ->
          ((((eq_ident i1 i2) && (eq_list eq_binder bs1 bs2)) &&
              (eq_option eq_term k1 k2))
             && (eq_list eq_term a1 a2))
            && (eq_tycon_record r1 r2)
      | (FStarC_Parser_AST.TyconVariant (i1, bs1, k1, cs1),
         FStarC_Parser_AST.TyconVariant (i2, bs2, k2, cs2)) ->
          (((eq_ident i1 i2) && (eq_list eq_binder bs1 bs2)) &&
             (eq_option eq_term k1 k2))
            &&
            (eq_list
               (fun uu___ ->
                  fun uu___1 ->
                    match (uu___, uu___1) with
                    | ((i11, o1, a1), (i21, o2, a2)) ->
                        ((eq_ident i11 i21) &&
                           (eq_option eq_constructor_payload o1 o2))
                          && (eq_list eq_term a1 a2)) cs1 cs2)
      | uu___ -> false
let (eq_lid : FStarC_Ident.lident -> FStarC_Ident.lident -> Prims.bool) =
  FStarC_Ident.lid_equals
let (eq_lift :
  FStarC_Parser_AST.lift -> FStarC_Parser_AST.lift -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      ((eq_lid t1.FStarC_Parser_AST.msource t2.FStarC_Parser_AST.msource) &&
         (eq_lid t1.FStarC_Parser_AST.mdest t2.FStarC_Parser_AST.mdest))
        &&
        (match ((t1.FStarC_Parser_AST.lift_op),
                 (t2.FStarC_Parser_AST.lift_op))
         with
         | (FStarC_Parser_AST.NonReifiableLift t11,
            FStarC_Parser_AST.NonReifiableLift t21) -> eq_term t11 t21
         | (FStarC_Parser_AST.ReifiableLift (t11, t21),
            FStarC_Parser_AST.ReifiableLift (t3, t4)) ->
             (eq_term t11 t3) && (eq_term t21 t4)
         | (FStarC_Parser_AST.LiftForFree t11, FStarC_Parser_AST.LiftForFree
            t21) -> eq_term t11 t21
         | uu___ -> false)
let (eq_pragma :
  FStarC_Parser_AST.pragma -> FStarC_Parser_AST.pragma -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (FStarC_Parser_AST.ShowOptions, FStarC_Parser_AST.ShowOptions) ->
          true
      | (FStarC_Parser_AST.SetOptions s1, FStarC_Parser_AST.SetOptions s2) ->
          s1 = s2
      | (FStarC_Parser_AST.ResetOptions s1, FStarC_Parser_AST.ResetOptions
         s2) -> eq_option (fun s11 -> fun s21 -> s11 = s21) s1 s2
      | (FStarC_Parser_AST.PushOptions s1, FStarC_Parser_AST.PushOptions s2)
          -> eq_option (fun s11 -> fun s21 -> s11 = s21) s1 s2
      | (FStarC_Parser_AST.PopOptions, FStarC_Parser_AST.PopOptions) -> true
      | (FStarC_Parser_AST.RestartSolver, FStarC_Parser_AST.RestartSolver) ->
          true
      | (FStarC_Parser_AST.PrintEffectsGraph,
         FStarC_Parser_AST.PrintEffectsGraph) -> true
      | uu___ -> false
let (eq_qualifier :
  FStarC_Parser_AST.qualifier -> FStarC_Parser_AST.qualifier -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (FStarC_Parser_AST.Private, FStarC_Parser_AST.Private) -> true
      | (FStarC_Parser_AST.Noeq, FStarC_Parser_AST.Noeq) -> true
      | (FStarC_Parser_AST.Unopteq, FStarC_Parser_AST.Unopteq) -> true
      | (FStarC_Parser_AST.Assumption, FStarC_Parser_AST.Assumption) -> true
      | (FStarC_Parser_AST.DefaultEffect, FStarC_Parser_AST.DefaultEffect) ->
          true
      | (FStarC_Parser_AST.TotalEffect, FStarC_Parser_AST.TotalEffect) ->
          true
      | (FStarC_Parser_AST.Effect_qual, FStarC_Parser_AST.Effect_qual) ->
          true
      | (FStarC_Parser_AST.New, FStarC_Parser_AST.New) -> true
      | (FStarC_Parser_AST.Inline, FStarC_Parser_AST.Inline) -> true
      | (FStarC_Parser_AST.Visible, FStarC_Parser_AST.Visible) -> true
      | (FStarC_Parser_AST.Unfold_for_unification_and_vcgen,
         FStarC_Parser_AST.Unfold_for_unification_and_vcgen) -> true
      | (FStarC_Parser_AST.Inline_for_extraction,
         FStarC_Parser_AST.Inline_for_extraction) -> true
      | (FStarC_Parser_AST.Irreducible, FStarC_Parser_AST.Irreducible) ->
          true
      | (FStarC_Parser_AST.NoExtract, FStarC_Parser_AST.NoExtract) -> true
      | (FStarC_Parser_AST.Reifiable, FStarC_Parser_AST.Reifiable) -> true
      | (FStarC_Parser_AST.Reflectable, FStarC_Parser_AST.Reflectable) ->
          true
      | (FStarC_Parser_AST.Opaque, FStarC_Parser_AST.Opaque) -> true
      | (FStarC_Parser_AST.Logic, FStarC_Parser_AST.Logic) -> true
      | uu___ -> false
let (eq_qualifiers :
  FStarC_Parser_AST.qualifiers -> FStarC_Parser_AST.qualifiers -> Prims.bool)
  = fun t1 -> fun t2 -> eq_list eq_qualifier t1 t2
let (eq_restriction :
  FStarC_Syntax_Syntax.restriction ->
    FStarC_Syntax_Syntax.restriction -> Prims.bool)
  =
  fun restriction1 ->
    fun restriction2 ->
      match (restriction1, restriction2) with
      | (FStarC_Syntax_Syntax.Unrestricted,
         FStarC_Syntax_Syntax.Unrestricted) -> true
      | (FStarC_Syntax_Syntax.AllowList l1, FStarC_Syntax_Syntax.AllowList
         l2) ->
          let eq_tuple eq_fst eq_snd uu___ uu___1 =
            match (uu___, uu___1) with
            | ((a, b), (c, d)) -> (eq_fst a c) && (eq_snd b d) in
          eq_list (eq_tuple eq_ident (eq_option eq_ident)) l1 l2
let rec (eq_decl' :
  FStarC_Parser_AST.decl' -> FStarC_Parser_AST.decl' -> Prims.bool) =
  fun d1 ->
    fun d2 ->
      match (d1, d2) with
      | (FStarC_Parser_AST.TopLevelModule lid1,
         FStarC_Parser_AST.TopLevelModule lid2) -> eq_lid lid1 lid2
      | (FStarC_Parser_AST.Open (lid1, restriction1), FStarC_Parser_AST.Open
         (lid2, restriction2)) ->
          (eq_lid lid1 lid2) && (eq_restriction restriction1 restriction2)
      | (FStarC_Parser_AST.Friend lid1, FStarC_Parser_AST.Friend lid2) ->
          eq_lid lid1 lid2
      | (FStarC_Parser_AST.Include (lid1, restriction1),
         FStarC_Parser_AST.Include (lid2, restriction2)) ->
          (eq_lid lid1 lid2) && (eq_restriction restriction1 restriction2)
      | (FStarC_Parser_AST.ModuleAbbrev (i1, lid1),
         FStarC_Parser_AST.ModuleAbbrev (i2, lid2)) ->
          (eq_ident i1 i2) && (eq_lid lid1 lid2)
      | (FStarC_Parser_AST.TopLevelLet (lq1, pats1),
         FStarC_Parser_AST.TopLevelLet (lq2, pats2)) ->
          (lq1 = lq2) &&
            (eq_list
               (fun uu___ ->
                  fun uu___1 ->
                    match (uu___, uu___1) with
                    | ((p1, t1), (p2, t2)) ->
                        (eq_pattern p1 p2) && (eq_term t1 t2)) pats1 pats2)
      | (FStarC_Parser_AST.Tycon (b1, b2, tcs1), FStarC_Parser_AST.Tycon
         (b3, b4, tcs2)) ->
          ((b1 = b3) && (b2 = b4)) && (eq_list eq_tycon tcs1 tcs2)
      | (FStarC_Parser_AST.Val (i1, t1), FStarC_Parser_AST.Val (i2, t2)) ->
          (eq_ident i1 i2) && (eq_term t1 t2)
      | (FStarC_Parser_AST.Exception (i1, t1), FStarC_Parser_AST.Exception
         (i2, t2)) -> (eq_ident i1 i2) && (eq_option eq_term t1 t2)
      | (FStarC_Parser_AST.NewEffect ed1, FStarC_Parser_AST.NewEffect ed2) ->
          eq_effect_decl ed1 ed2
      | (FStarC_Parser_AST.LayeredEffect ed1, FStarC_Parser_AST.LayeredEffect
         ed2) -> eq_effect_decl ed1 ed2
      | (FStarC_Parser_AST.SubEffect l1, FStarC_Parser_AST.SubEffect l2) ->
          eq_lift l1 l2
      | (FStarC_Parser_AST.Polymonadic_bind (lid1, lid2, lid3, t1),
         FStarC_Parser_AST.Polymonadic_bind (lid4, lid5, lid6, t2)) ->
          (((eq_lid lid1 lid4) && (eq_lid lid2 lid5)) && (eq_lid lid3 lid6))
            && (eq_term t1 t2)
      | (FStarC_Parser_AST.Polymonadic_subcomp (lid1, lid2, t1),
         FStarC_Parser_AST.Polymonadic_subcomp (lid3, lid4, t2)) ->
          ((eq_lid lid1 lid3) && (eq_lid lid2 lid4)) && (eq_term t1 t2)
      | (FStarC_Parser_AST.Pragma p1, FStarC_Parser_AST.Pragma p2) ->
          eq_pragma p1 p2
      | (FStarC_Parser_AST.Assume (i1, t1), FStarC_Parser_AST.Assume
         (i2, t2)) -> (eq_ident i1 i2) && (eq_term t1 t2)
      | (FStarC_Parser_AST.Splice (is_typed1, is1, t1),
         FStarC_Parser_AST.Splice (is_typed2, is2, t2)) ->
          ((is_typed1 = is_typed2) && (eq_list eq_ident is1 is2)) &&
            (eq_term t1 t2)
      | (FStarC_Parser_AST.DeclSyntaxExtension (s1, t1, uu___, uu___1),
         FStarC_Parser_AST.DeclSyntaxExtension (s2, t2, uu___2, uu___3)) ->
          (s1 = s2) && (t1 = t2)
      | (FStarC_Parser_AST.UseLangDecls p1, FStarC_Parser_AST.UseLangDecls
         p2) -> p1 = p2
      | (FStarC_Parser_AST.DeclToBeDesugared tbs1,
         FStarC_Parser_AST.DeclToBeDesugared tbs2) ->
          (tbs1.FStarC_Parser_AST.lang_name =
             tbs2.FStarC_Parser_AST.lang_name)
            &&
            (tbs1.FStarC_Parser_AST.eq tbs1.FStarC_Parser_AST.blob
               tbs2.FStarC_Parser_AST.blob)
      | uu___ -> false
and (eq_effect_decl :
  FStarC_Parser_AST.effect_decl ->
    FStarC_Parser_AST.effect_decl -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      match (t1, t2) with
      | (FStarC_Parser_AST.DefineEffect (i1, bs1, t11, ds1),
         FStarC_Parser_AST.DefineEffect (i2, bs2, t21, ds2)) ->
          (((eq_ident i1 i2) && (eq_list eq_binder bs1 bs2)) &&
             (eq_term t11 t21))
            && (eq_list eq_decl ds1 ds2)
      | (FStarC_Parser_AST.RedefineEffect (i1, bs1, t11),
         FStarC_Parser_AST.RedefineEffect (i2, bs2, t21)) ->
          ((eq_ident i1 i2) && (eq_list eq_binder bs1 bs2)) &&
            (eq_term t11 t21)
      | uu___ -> false
and (eq_decl :
  FStarC_Parser_AST.decl -> FStarC_Parser_AST.decl -> Prims.bool) =
  fun d1 ->
    fun d2 ->
      ((eq_decl' d1.FStarC_Parser_AST.d d2.FStarC_Parser_AST.d) &&
         (eq_list eq_qualifier d1.FStarC_Parser_AST.quals
            d2.FStarC_Parser_AST.quals))
        &&
        (eq_list eq_term d1.FStarC_Parser_AST.attrs
           d2.FStarC_Parser_AST.attrs)
let concat_map :
  'uuuuu 'uuuuu1 .
    unit ->
      ('uuuuu -> 'uuuuu1 Prims.list) ->
        'uuuuu Prims.list -> 'uuuuu1 Prims.list
  = fun uu___ -> FStarC_Compiler_List.collect
let opt_map :
  'uuuuu 'a .
    ('a -> 'uuuuu Prims.list) ->
      'a FStar_Pervasives_Native.option -> 'uuuuu Prims.list
  =
  fun f ->
    fun x ->
      match x with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some x1 -> f x1
let rec (lidents_of_term :
  FStarC_Parser_AST.term -> FStarC_Ident.lident Prims.list) =
  fun t -> lidents_of_term' t.FStarC_Parser_AST.tm
and (lidents_of_term' :
  FStarC_Parser_AST.term' -> FStarC_Ident.lident Prims.list) =
  fun t ->
    match t with
    | FStarC_Parser_AST.Wild -> []
    | FStarC_Parser_AST.Const uu___ -> []
    | FStarC_Parser_AST.Op (s, ts) -> (concat_map ()) lidents_of_term ts
    | FStarC_Parser_AST.Tvar uu___ -> []
    | FStarC_Parser_AST.Uvar uu___ -> []
    | FStarC_Parser_AST.Var lid -> [lid]
    | FStarC_Parser_AST.Name lid -> [lid]
    | FStarC_Parser_AST.Projector (lid, uu___) -> [lid]
    | FStarC_Parser_AST.Construct (lid, ts) ->
        let uu___ =
          (concat_map ())
            (fun uu___1 ->
               match uu___1 with | (t1, uu___2) -> lidents_of_term t1) ts in
        lid :: uu___
    | FStarC_Parser_AST.Function (brs, uu___) ->
        (concat_map ()) lidents_of_branch brs
    | FStarC_Parser_AST.Abs (ps, t1) ->
        let uu___ = (concat_map ()) lidents_of_pattern ps in
        let uu___1 = lidents_of_term t1 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.App (t1, t2, uu___) ->
        let uu___1 = lidents_of_term t1 in
        let uu___2 = lidents_of_term t2 in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Parser_AST.Let (uu___, lbs, t1) ->
        let uu___1 =
          (concat_map ())
            (fun uu___2 ->
               match uu___2 with
               | (uu___3, (p, t2)) ->
                   let uu___4 = lidents_of_pattern p in
                   let uu___5 = lidents_of_term t2 in
                   FStarC_Compiler_List.op_At uu___4 uu___5) lbs in
        let uu___2 = lidents_of_term t1 in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Parser_AST.LetOperator (lbs, t1) ->
        let uu___ =
          (concat_map ())
            (fun uu___1 ->
               match uu___1 with
               | (uu___2, p, t2) ->
                   let uu___3 = lidents_of_pattern p in
                   let uu___4 = lidents_of_term t2 in
                   FStarC_Compiler_List.op_At uu___3 uu___4) lbs in
        let uu___1 = lidents_of_term t1 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.LetOpen (lid, t1) ->
        let uu___ = lidents_of_term t1 in lid :: uu___
    | FStarC_Parser_AST.LetOpenRecord (t1, t2, t3) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 = lidents_of_term t3 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.Seq (t1, t2) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 = lidents_of_term t2 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.Bind (uu___, t1, t2) ->
        let uu___1 = lidents_of_term t1 in
        let uu___2 = lidents_of_term t2 in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Parser_AST.If (t1, uu___, uu___1, t2, t3) ->
        let uu___2 = lidents_of_term t1 in
        let uu___3 =
          let uu___4 = lidents_of_term t2 in
          let uu___5 = lidents_of_term t3 in
          FStarC_Compiler_List.op_At uu___4 uu___5 in
        FStarC_Compiler_List.op_At uu___2 uu___3
    | FStarC_Parser_AST.Match (t1, uu___, uu___1, bs) ->
        let uu___2 = lidents_of_term t1 in
        let uu___3 = (concat_map ()) lidents_of_branch bs in
        FStarC_Compiler_List.op_At uu___2 uu___3
    | FStarC_Parser_AST.TryWith (t1, bs) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 = (concat_map ()) lidents_of_branch bs in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.Ascribed (t1, t2, uu___, uu___1) ->
        let uu___2 = lidents_of_term t1 in
        let uu___3 = lidents_of_term t2 in
        FStarC_Compiler_List.op_At uu___2 uu___3
    | FStarC_Parser_AST.Record (t1, ts) ->
        let uu___ =
          (concat_map ())
            (fun uu___1 ->
               match uu___1 with | (uu___2, t2) -> lidents_of_term t2) ts in
        let uu___1 = opt_map lidents_of_term t1 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.Project (t1, uu___) -> lidents_of_term t1
    | FStarC_Parser_AST.Product (ts, t1) ->
        let uu___ = (concat_map ()) lidents_of_binder ts in
        let uu___1 = lidents_of_term t1 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.Sum (ts, t1) ->
        let uu___ =
          (concat_map ())
            (fun uu___1 ->
               match uu___1 with
               | FStar_Pervasives.Inl b -> lidents_of_binder b
               | FStar_Pervasives.Inr t2 -> lidents_of_term t2) ts in
        let uu___1 = lidents_of_term t1 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.QForall (bs, _pats, t1) -> lidents_of_term t1
    | FStarC_Parser_AST.QExists (bs, _pats, t1) -> lidents_of_term t1
    | FStarC_Parser_AST.QuantOp (i, bs, pats, t1) -> lidents_of_term t1
    | FStarC_Parser_AST.Refine (b, t1) -> lidents_of_term t1
    | FStarC_Parser_AST.NamedTyp (i, t1) -> lidents_of_term t1
    | FStarC_Parser_AST.Paren t1 -> lidents_of_term t1
    | FStarC_Parser_AST.Requires (t1, uu___) -> lidents_of_term t1
    | FStarC_Parser_AST.Ensures (t1, uu___) -> lidents_of_term t1
    | FStarC_Parser_AST.LexList ts -> (concat_map ()) lidents_of_term ts
    | FStarC_Parser_AST.WFOrder (t1, t2) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 = lidents_of_term t2 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.Decreases (t1, uu___) -> lidents_of_term t1
    | FStarC_Parser_AST.Labeled (t1, uu___, uu___1) -> lidents_of_term t1
    | FStarC_Parser_AST.Discrim lid -> [lid]
    | FStarC_Parser_AST.Attributes ts -> (concat_map ()) lidents_of_term ts
    | FStarC_Parser_AST.Antiquote t1 -> lidents_of_term t1
    | FStarC_Parser_AST.Quote (t1, uu___) -> lidents_of_term t1
    | FStarC_Parser_AST.VQuote t1 -> lidents_of_term t1
    | FStarC_Parser_AST.CalcProof (t1, t2, ts) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 = (concat_map ()) lidents_of_calc_step ts in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.IntroForall (bs, t1, t2) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 = lidents_of_term t2 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.IntroExists (bs, t1, ts, t2) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = (concat_map ()) lidents_of_term ts in
          let uu___3 = lidents_of_term t2 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.IntroImplies (t1, t2, b, t3) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 = lidents_of_term t3 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.IntroOr (b, t1, t2, t3) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 = lidents_of_term t3 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.IntroAnd (t1, t2, t3, t4) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 =
            let uu___4 = lidents_of_term t3 in
            let uu___5 = lidents_of_term t4 in
            FStarC_Compiler_List.op_At uu___4 uu___5 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.ElimForall (bs, t1, ts) ->
        let uu___ = (concat_map ()) lidents_of_binder bs in
        let uu___1 =
          let uu___2 = lidents_of_term t1 in
          let uu___3 = (concat_map ()) lidents_of_term ts in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.ElimExists (bs, t1, t2, b, t3) ->
        let uu___ = (concat_map ()) lidents_of_binder bs in
        let uu___1 =
          let uu___2 = lidents_of_term t1 in
          let uu___3 =
            let uu___4 = lidents_of_term t2 in
            let uu___5 = lidents_of_term t3 in
            FStarC_Compiler_List.op_At uu___4 uu___5 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.ElimImplies (t1, t2, t3) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 = lidents_of_term t3 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.ElimOr (t1, t2, t3, b1, t4, b2, t5) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 =
            let uu___4 = lidents_of_term t3 in
            let uu___5 =
              let uu___6 = lidents_of_term t4 in
              let uu___7 = lidents_of_term t5 in
              FStarC_Compiler_List.op_At uu___6 uu___7 in
            FStarC_Compiler_List.op_At uu___4 uu___5 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.ElimAnd (t1, t2, t3, b1, b2, t4) ->
        let uu___ = lidents_of_term t1 in
        let uu___1 =
          let uu___2 = lidents_of_term t2 in
          let uu___3 =
            let uu___4 = lidents_of_term t3 in
            let uu___5 = lidents_of_term t4 in
            FStarC_Compiler_List.op_At uu___4 uu___5 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.ListLiteral ts -> (concat_map ()) lidents_of_term ts
    | FStarC_Parser_AST.SeqLiteral ts -> (concat_map ()) lidents_of_term ts
and (lidents_of_branch :
  (FStarC_Parser_AST.pattern * FStarC_Parser_AST.term
    FStar_Pervasives_Native.option * FStarC_Parser_AST.term) ->
    FStarC_Ident.lident Prims.list)
  =
  fun uu___ ->
    match uu___ with
    | (p, uu___1, t) ->
        let uu___2 = lidents_of_pattern p in
        let uu___3 = lidents_of_term t in
        FStarC_Compiler_List.op_At uu___2 uu___3
and (lidents_of_calc_step :
  FStarC_Parser_AST.calc_step -> FStarC_Ident.lident Prims.list) =
  fun uu___ ->
    match uu___ with
    | FStarC_Parser_AST.CalcStep (t1, t2, t3) ->
        let uu___1 = lidents_of_term t1 in
        let uu___2 =
          let uu___3 = lidents_of_term t2 in
          let uu___4 = lidents_of_term t3 in
          FStarC_Compiler_List.op_At uu___3 uu___4 in
        FStarC_Compiler_List.op_At uu___1 uu___2
and (lidents_of_pattern :
  FStarC_Parser_AST.pattern -> FStarC_Ident.lident Prims.list) =
  fun p ->
    match p.FStarC_Parser_AST.pat with
    | FStarC_Parser_AST.PatWild uu___ -> []
    | FStarC_Parser_AST.PatConst uu___ -> []
    | FStarC_Parser_AST.PatApp (p1, ps) ->
        let uu___ = lidents_of_pattern p1 in
        let uu___1 = (concat_map ()) lidents_of_pattern ps in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.PatVar (i, uu___, uu___1) ->
        let uu___2 = FStarC_Ident.lid_of_ids [i] in [uu___2]
    | FStarC_Parser_AST.PatName lid -> [lid]
    | FStarC_Parser_AST.PatTvar (i, uu___, uu___1) -> []
    | FStarC_Parser_AST.PatList ps -> (concat_map ()) lidents_of_pattern ps
    | FStarC_Parser_AST.PatTuple (ps, uu___) ->
        (concat_map ()) lidents_of_pattern ps
    | FStarC_Parser_AST.PatRecord ps ->
        (concat_map ())
          (fun uu___ ->
             match uu___ with | (uu___1, p1) -> lidents_of_pattern p1) ps
    | FStarC_Parser_AST.PatAscribed (p1, (t1, t2)) ->
        let uu___ = lidents_of_pattern p1 in
        let uu___1 =
          let uu___2 = lidents_of_term t1 in
          let uu___3 = opt_map lidents_of_term t2 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Parser_AST.PatOr ps -> (concat_map ()) lidents_of_pattern ps
    | FStarC_Parser_AST.PatOp uu___ -> []
    | FStarC_Parser_AST.PatVQuote t -> lidents_of_term t
and (lidents_of_binder :
  FStarC_Parser_AST.binder -> FStarC_Ident.lident Prims.list) =
  fun b ->
    match b.FStarC_Parser_AST.b with
    | FStarC_Parser_AST.Annotated (uu___, t) -> lidents_of_term t
    | FStarC_Parser_AST.TAnnotated (uu___, t) -> lidents_of_term t
    | FStarC_Parser_AST.NoName t -> lidents_of_term t
    | uu___ -> []
let lidents_of_tycon_record :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu * 'uuuuu1 * 'uuuuu2 * FStarC_Parser_AST.term) ->
      FStarC_Ident.lident Prims.list
  =
  fun uu___ ->
    match uu___ with | (uu___1, uu___2, uu___3, t) -> lidents_of_term t
let (lidents_of_constructor_payload :
  FStarC_Parser_AST.constructor_payload -> FStarC_Ident.lident Prims.list) =
  fun t ->
    match t with
    | FStarC_Parser_AST.VpOfNotation t1 -> lidents_of_term t1
    | FStarC_Parser_AST.VpArbitrary t1 -> lidents_of_term t1
    | FStarC_Parser_AST.VpRecord (tc, FStar_Pervasives_Native.None) ->
        (concat_map ()) lidents_of_tycon_record tc
    | FStarC_Parser_AST.VpRecord (tc, FStar_Pervasives_Native.Some t1) ->
        let uu___ = (concat_map ()) lidents_of_tycon_record tc in
        let uu___1 = lidents_of_term t1 in
        FStarC_Compiler_List.op_At uu___ uu___1
let (lidents_of_tycon_variant :
  (FStarC_Ident.ident * FStarC_Parser_AST.constructor_payload
    FStar_Pervasives_Native.option * FStarC_Parser_AST.attributes_) ->
    FStarC_Ident.lident Prims.list)
  =
  fun tc ->
    match tc with
    | (uu___, FStar_Pervasives_Native.None, uu___1) -> []
    | (uu___, FStar_Pervasives_Native.Some t, uu___1) ->
        lidents_of_constructor_payload t
let (lidents_of_tycon :
  FStarC_Parser_AST.tycon -> FStarC_Ident.lident Prims.list) =
  fun tc ->
    match tc with
    | FStarC_Parser_AST.TyconAbstract (uu___, bs, k) ->
        let uu___1 = (concat_map ()) lidents_of_binder bs in
        let uu___2 = opt_map lidents_of_term k in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Parser_AST.TyconAbbrev (uu___, bs, k, t) ->
        let uu___1 = (concat_map ()) lidents_of_binder bs in
        let uu___2 =
          let uu___3 = opt_map lidents_of_term k in
          let uu___4 = lidents_of_term t in
          FStarC_Compiler_List.op_At uu___3 uu___4 in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Parser_AST.TyconRecord (uu___, bs, k, uu___1, tcs) ->
        let uu___2 = (concat_map ()) lidents_of_binder bs in
        let uu___3 =
          let uu___4 = opt_map lidents_of_term k in
          let uu___5 = (concat_map ()) lidents_of_tycon_record tcs in
          FStarC_Compiler_List.op_At uu___4 uu___5 in
        FStarC_Compiler_List.op_At uu___2 uu___3
    | FStarC_Parser_AST.TyconVariant (uu___, bs, k, tcs) ->
        let uu___1 = (concat_map ()) lidents_of_binder bs in
        let uu___2 =
          let uu___3 = opt_map lidents_of_term k in
          let uu___4 = (concat_map ()) lidents_of_tycon_variant tcs in
          FStarC_Compiler_List.op_At uu___3 uu___4 in
        FStarC_Compiler_List.op_At uu___1 uu___2
let (lidents_of_lift :
  FStarC_Parser_AST.lift -> FStarC_Ident.lident Prims.list) =
  fun l ->
    let uu___ =
      match l.FStarC_Parser_AST.lift_op with
      | FStarC_Parser_AST.NonReifiableLift t -> lidents_of_term t
      | FStarC_Parser_AST.ReifiableLift (t1, t2) ->
          let uu___1 = lidents_of_term t1 in
          let uu___2 = lidents_of_term t2 in
          FStarC_Compiler_List.op_At uu___1 uu___2
      | FStarC_Parser_AST.LiftForFree t -> lidents_of_term t in
    FStarC_Compiler_List.op_At
      [l.FStarC_Parser_AST.msource; l.FStarC_Parser_AST.mdest] uu___
let rec (lidents_of_decl :
  FStarC_Parser_AST.decl -> FStarC_Ident.lident Prims.list) =
  fun d ->
    match d.FStarC_Parser_AST.d with
    | FStarC_Parser_AST.TopLevelModule uu___ -> []
    | FStarC_Parser_AST.Open (l, uu___) -> [l]
    | FStarC_Parser_AST.Friend l -> [l]
    | FStarC_Parser_AST.Include (l, uu___) -> [l]
    | FStarC_Parser_AST.ModuleAbbrev (uu___, l) -> [l]
    | FStarC_Parser_AST.TopLevelLet (_q, lbs) ->
        (concat_map ())
          (fun uu___ ->
             match uu___ with
             | (p, t) ->
                 let uu___1 = lidents_of_pattern p in
                 let uu___2 = lidents_of_term t in
                 FStarC_Compiler_List.op_At uu___1 uu___2) lbs
    | FStarC_Parser_AST.Tycon (uu___, uu___1, tcs) ->
        (concat_map ()) lidents_of_tycon tcs
    | FStarC_Parser_AST.Val (uu___, t) -> lidents_of_term t
    | FStarC_Parser_AST.Exception (uu___, FStar_Pervasives_Native.None) -> []
    | FStarC_Parser_AST.Exception (uu___, FStar_Pervasives_Native.Some t) ->
        lidents_of_term t
    | FStarC_Parser_AST.NewEffect ed -> lidents_of_effect_decl ed
    | FStarC_Parser_AST.LayeredEffect ed -> lidents_of_effect_decl ed
    | FStarC_Parser_AST.SubEffect lift -> lidents_of_lift lift
    | FStarC_Parser_AST.Polymonadic_bind (l0, l1, l2, t) ->
        let uu___ =
          let uu___1 = let uu___2 = lidents_of_term t in l2 :: uu___2 in l1
            :: uu___1 in
        l0 :: uu___
    | FStarC_Parser_AST.Polymonadic_subcomp (l0, l1, t) ->
        let uu___ = let uu___1 = lidents_of_term t in l1 :: uu___1 in l0 ::
          uu___
    | FStarC_Parser_AST.Pragma uu___ -> []
    | FStarC_Parser_AST.Assume (uu___, t) -> lidents_of_term t
    | FStarC_Parser_AST.Splice (uu___, uu___1, t) -> lidents_of_term t
    | FStarC_Parser_AST.DeclSyntaxExtension uu___ -> []
    | FStarC_Parser_AST.DeclToBeDesugared uu___ -> []
and (lidents_of_effect_decl :
  FStarC_Parser_AST.effect_decl -> FStarC_Ident.lident Prims.list) =
  fun ed ->
    match ed with
    | FStarC_Parser_AST.DefineEffect (uu___, bs, t, ds) ->
        let uu___1 = (concat_map ()) lidents_of_binder bs in
        let uu___2 =
          let uu___3 = lidents_of_term t in
          let uu___4 = (concat_map ()) lidents_of_decl ds in
          FStarC_Compiler_List.op_At uu___3 uu___4 in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Parser_AST.RedefineEffect (uu___, bs, t) ->
        let uu___1 = (concat_map ()) lidents_of_binder bs in
        let uu___2 = lidents_of_term t in
        FStarC_Compiler_List.op_At uu___1 uu___2
type open_namespaces_and_abbreviations =
  {
  open_namespaces: FStarC_Ident.lident Prims.list ;
  module_abbreviations: (FStarC_Ident.ident * FStarC_Ident.lident) Prims.list }
let (__proj__Mkopen_namespaces_and_abbreviations__item__open_namespaces :
  open_namespaces_and_abbreviations -> FStarC_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with
    | { open_namespaces; module_abbreviations;_} -> open_namespaces
let (__proj__Mkopen_namespaces_and_abbreviations__item__module_abbreviations
  :
  open_namespaces_and_abbreviations ->
    (FStarC_Ident.ident * FStarC_Ident.lident) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { open_namespaces; module_abbreviations;_} -> module_abbreviations
type error_message =
  {
  message: Prims.string ;
  range: FStarC_Compiler_Range_Type.range }
let (__proj__Mkerror_message__item__message : error_message -> Prims.string)
  = fun projectee -> match projectee with | { message; range;_} -> message
let (__proj__Mkerror_message__item__range :
  error_message -> FStarC_Compiler_Range_Type.range) =
  fun projectee -> match projectee with | { message; range;_} -> range
type extension_parser =
  {
  parse_decl_name:
    Prims.string ->
      FStarC_Compiler_Range_Type.range ->
        (error_message, FStarC_Ident.ident) FStar_Pervasives.either
    ;
  parse_decl:
    open_namespaces_and_abbreviations ->
      Prims.string ->
        FStarC_Compiler_Range_Type.range ->
          (error_message, FStarC_Parser_AST.decl) FStar_Pervasives.either
    }
let (__proj__Mkextension_parser__item__parse_decl_name :
  extension_parser ->
    Prims.string ->
      FStarC_Compiler_Range_Type.range ->
        (error_message, FStarC_Ident.ident) FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with
    | { parse_decl_name; parse_decl;_} -> parse_decl_name
let (__proj__Mkextension_parser__item__parse_decl :
  extension_parser ->
    open_namespaces_and_abbreviations ->
      Prims.string ->
        FStarC_Compiler_Range_Type.range ->
          (error_message, FStarC_Parser_AST.decl) FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with | { parse_decl_name; parse_decl;_} -> parse_decl
let (extension_parser_table : extension_parser FStarC_Compiler_Util.smap) =
  FStarC_Compiler_Util.smap_create (Prims.of_int (20))
let (register_extension_parser : Prims.string -> extension_parser -> unit) =
  fun ext ->
    fun parser ->
      FStarC_Compiler_Util.smap_add extension_parser_table ext parser
let (lookup_extension_parser :
  Prims.string -> extension_parser FStar_Pervasives_Native.option) =
  fun ext ->
    let do1 uu___ =
      FStarC_Compiler_Util.smap_try_find extension_parser_table ext in
    let uu___ = do1 () in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        let uu___1 = FStarC_Compiler_Plugins.autoload_plugin ext in
        if uu___1 then do1 () else FStar_Pervasives_Native.None
    | r -> r
type extension_lang_parser =
  {
  parse_decls:
    Prims.string ->
      FStarC_Compiler_Range_Type.range ->
        (error_message, FStarC_Parser_AST.decl Prims.list)
          FStar_Pervasives.either
    }
let (__proj__Mkextension_lang_parser__item__parse_decls :
  extension_lang_parser ->
    Prims.string ->
      FStarC_Compiler_Range_Type.range ->
        (error_message, FStarC_Parser_AST.decl Prims.list)
          FStar_Pervasives.either)
  = fun projectee -> match projectee with | { parse_decls;_} -> parse_decls
let (as_open_namespaces_and_abbrevs :
  FStarC_Parser_AST.decl Prims.list -> open_namespaces_and_abbreviations) =
  fun ls ->
    FStarC_Compiler_List.fold_right
      (fun d ->
         fun out ->
           match d.FStarC_Parser_AST.d with
           | FStarC_Parser_AST.Open (lid, uu___) ->
               {
                 open_namespaces = (lid :: (out.open_namespaces));
                 module_abbreviations = (out.module_abbreviations)
               }
           | FStarC_Parser_AST.ModuleAbbrev (i, lid) ->
               {
                 open_namespaces = (out.open_namespaces);
                 module_abbreviations = ((i, lid) ::
                   (out.module_abbreviations))
               }
           | uu___ -> out) ls
      { open_namespaces = []; module_abbreviations = [] }
let (extension_lang_parser_table :
  extension_lang_parser FStarC_Compiler_Util.smap) =
  FStarC_Compiler_Util.smap_create (Prims.of_int (20))
let (register_extension_lang_parser :
  Prims.string -> extension_lang_parser -> unit) =
  fun ext ->
    fun parser ->
      FStarC_Compiler_Util.smap_add extension_lang_parser_table ext parser
let (lookup_extension_lang_parser :
  Prims.string -> extension_lang_parser FStar_Pervasives_Native.option) =
  fun ext ->
    let r =
      FStarC_Compiler_Util.smap_try_find extension_lang_parser_table ext in
    match r with
    | FStar_Pervasives_Native.None ->
        let uu___ = FStarC_Compiler_Plugins.autoload_plugin ext in
        if uu___
        then
          FStarC_Compiler_Util.smap_try_find extension_lang_parser_table ext
        else FStar_Pervasives_Native.None
    | uu___ -> r
let (parse_extension_lang :
  Prims.string ->
    Prims.string ->
      FStarC_Compiler_Range_Type.range -> FStarC_Parser_AST.decl Prims.list)
  =
  fun lang_name ->
    fun raw_text ->
      fun raw_text_pos ->
        let extension_parser1 = lookup_extension_lang_parser lang_name in
        match extension_parser1 with
        | FStar_Pervasives_Native.None ->
            let uu___ =
              FStarC_Compiler_Util.format1 "Unknown language extension %s"
                lang_name in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
              raw_text_pos FStarC_Errors_Codes.Fatal_SyntaxError ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___)
        | FStar_Pervasives_Native.Some parser ->
            let uu___ = parser.parse_decls raw_text raw_text_pos in
            (match uu___ with
             | FStar_Pervasives.Inl error ->
                 FStarC_Errors.raise_error
                   FStarC_Class_HasRange.hasRange_range error.range
                   FStarC_Errors_Codes.Fatal_SyntaxError ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic error.message)
             | FStar_Pervasives.Inr ds -> ds)