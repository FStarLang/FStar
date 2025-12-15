open Prims
let concat_map (uu___ : unit) :
  ('uuuuu -> 'uuuuu1 Prims.list) -> 'uuuuu Prims.list -> 'uuuuu1 Prims.list=
  FStarC_List.collect
let opt_map (f : 'a -> 'uuuuu Prims.list)
  (x : 'a FStar_Pervasives_Native.option) : 'uuuuu Prims.list=
  match x with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some x1 -> f x1
let rec lidents_of_term (t : FStarC_Parser_AST.term) :
  FStarC_Ident.lident Prims.list= lidents_of_term' t.FStarC_Parser_AST.tm
and lidents_of_term' (t : FStarC_Parser_AST.term') :
  FStarC_Ident.lident Prims.list=
  match t with
  | FStarC_Parser_AST.Wild -> []
  | FStarC_Parser_AST.Const uu___ -> []
  | FStarC_Parser_AST.Op (s, ts) -> (concat_map ()) lidents_of_term ts
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
      let uu___1 = lidents_of_term t1 in FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.App (t1, t2, uu___) ->
      let uu___1 = lidents_of_term t1 in
      let uu___2 = lidents_of_term t2 in FStarC_List.op_At uu___1 uu___2
  | FStarC_Parser_AST.Let (uu___, lbs, t1) ->
      let uu___1 =
        (concat_map ())
          (fun uu___2 ->
             match uu___2 with
             | (uu___3, (p, t2)) ->
                 let uu___4 = lidents_of_pattern p in
                 let uu___5 = lidents_of_term t2 in
                 FStarC_List.op_At uu___4 uu___5) lbs in
      let uu___2 = lidents_of_term t1 in FStarC_List.op_At uu___1 uu___2
  | FStarC_Parser_AST.LetOperator (lbs, t1) ->
      let uu___ =
        (concat_map ())
          (fun uu___1 ->
             match uu___1 with
             | (uu___2, p, t2) ->
                 let uu___3 = lidents_of_pattern p in
                 let uu___4 = lidents_of_term t2 in
                 FStarC_List.op_At uu___3 uu___4) lbs in
      let uu___1 = lidents_of_term t1 in FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.LetOpen (lid, t1) ->
      let uu___ = lidents_of_term t1 in lid :: uu___
  | FStarC_Parser_AST.LetOpenRecord (t1, t2, t3) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = lidents_of_term t2 in
        let uu___3 = lidents_of_term t3 in FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.Seq (t1, t2) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 = lidents_of_term t2 in FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.Bind (uu___, t1, t2) ->
      let uu___1 = lidents_of_term t1 in
      let uu___2 = lidents_of_term t2 in FStarC_List.op_At uu___1 uu___2
  | FStarC_Parser_AST.If (t1, uu___, uu___1, t2, t3) ->
      let uu___2 = lidents_of_term t1 in
      let uu___3 =
        let uu___4 = lidents_of_term t2 in
        let uu___5 = lidents_of_term t3 in FStarC_List.op_At uu___4 uu___5 in
      FStarC_List.op_At uu___2 uu___3
  | FStarC_Parser_AST.Match (t1, uu___, uu___1, bs) ->
      let uu___2 = lidents_of_term t1 in
      let uu___3 = (concat_map ()) lidents_of_branch bs in
      FStarC_List.op_At uu___2 uu___3
  | FStarC_Parser_AST.TryWith (t1, bs) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 = (concat_map ()) lidents_of_branch bs in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.Ascribed (t1, t2, uu___, uu___1) ->
      let uu___2 = lidents_of_term t1 in
      let uu___3 = lidents_of_term t2 in FStarC_List.op_At uu___2 uu___3
  | FStarC_Parser_AST.Record (t1, ts) ->
      let uu___ =
        (concat_map ())
          (fun uu___1 ->
             match uu___1 with | (uu___2, t2) -> lidents_of_term t2) ts in
      let uu___1 = opt_map lidents_of_term t1 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.Project (t1, uu___) -> lidents_of_term t1
  | FStarC_Parser_AST.Product (ts, t1) ->
      let uu___ = (concat_map ()) lidents_of_binder ts in
      let uu___1 = lidents_of_term t1 in FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.Sum (ts, t1) ->
      let uu___ =
        (concat_map ())
          (fun uu___1 ->
             match uu___1 with
             | FStar_Pervasives.Inl b -> lidents_of_binder b
             | FStar_Pervasives.Inr t2 -> lidents_of_term t2) ts in
      let uu___1 = lidents_of_term t1 in FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.QForall (bs, _pats, t1) -> lidents_of_term t1
  | FStarC_Parser_AST.QExists (bs, _pats, t1) -> lidents_of_term t1
  | FStarC_Parser_AST.QuantOp (i, bs, pats, t1) -> lidents_of_term t1
  | FStarC_Parser_AST.Refine (b, t1) -> lidents_of_term t1
  | FStarC_Parser_AST.NamedTyp (i, t1) -> lidents_of_term t1
  | FStarC_Parser_AST.Paren t1 -> lidents_of_term t1
  | FStarC_Parser_AST.Requires t1 -> lidents_of_term t1
  | FStarC_Parser_AST.Ensures t1 -> lidents_of_term t1
  | FStarC_Parser_AST.LexList ts -> (concat_map ()) lidents_of_term ts
  | FStarC_Parser_AST.WFOrder (t1, t2) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 = lidents_of_term t2 in FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.Decreases t1 -> lidents_of_term t1
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
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.IntroForall (bs, t1, t2) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 = lidents_of_term t2 in FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.IntroExists (bs, t1, ts, t2) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = (concat_map ()) lidents_of_term ts in
        let uu___3 = lidents_of_term t2 in FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.IntroImplies (t1, t2, b, t3) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = lidents_of_term t2 in
        let uu___3 = lidents_of_term t3 in FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.IntroOr (b, t1, t2, t3) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = lidents_of_term t2 in
        let uu___3 = lidents_of_term t3 in FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.IntroAnd (t1, t2, t3, t4) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = lidents_of_term t2 in
        let uu___3 =
          let uu___4 = lidents_of_term t3 in
          let uu___5 = lidents_of_term t4 in FStarC_List.op_At uu___4 uu___5 in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.ElimForall (bs, t1, ts) ->
      let uu___ = (concat_map ()) lidents_of_binder bs in
      let uu___1 =
        let uu___2 = lidents_of_term t1 in
        let uu___3 = (concat_map ()) lidents_of_term ts in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.ElimExists (bs, t1, t2, b, t3) ->
      let uu___ = (concat_map ()) lidents_of_binder bs in
      let uu___1 =
        let uu___2 = lidents_of_term t1 in
        let uu___3 =
          let uu___4 = lidents_of_term t2 in
          let uu___5 = lidents_of_term t3 in FStarC_List.op_At uu___4 uu___5 in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.ElimImplies (t1, t2, t3) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = lidents_of_term t2 in
        let uu___3 = lidents_of_term t3 in FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.ElimOr (t1, t2, t3, b1, t4, b2, t5) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = lidents_of_term t2 in
        let uu___3 =
          let uu___4 = lidents_of_term t3 in
          let uu___5 =
            let uu___6 = lidents_of_term t4 in
            let uu___7 = lidents_of_term t5 in
            FStarC_List.op_At uu___6 uu___7 in
          FStarC_List.op_At uu___4 uu___5 in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.ElimAnd (t1, t2, t3, b1, b2, t4) ->
      let uu___ = lidents_of_term t1 in
      let uu___1 =
        let uu___2 = lidents_of_term t2 in
        let uu___3 =
          let uu___4 = lidents_of_term t3 in
          let uu___5 = lidents_of_term t4 in FStarC_List.op_At uu___4 uu___5 in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.ListLiteral ts -> (concat_map ()) lidents_of_term ts
  | FStarC_Parser_AST.SeqLiteral ts -> (concat_map ()) lidents_of_term ts
and lidents_of_branch
  (uu___ :
    (FStarC_Parser_AST.pattern * FStarC_Parser_AST.term
      FStar_Pervasives_Native.option * FStarC_Parser_AST.term))
  : FStarC_Ident.lident Prims.list=
  match uu___ with
  | (p, uu___1, t) ->
      let uu___2 = lidents_of_pattern p in
      let uu___3 = lidents_of_term t in FStarC_List.op_At uu___2 uu___3
and lidents_of_calc_step (uu___ : FStarC_Parser_AST.calc_step) :
  FStarC_Ident.lident Prims.list=
  match uu___ with
  | FStarC_Parser_AST.CalcStep (t1, t2, t3) ->
      let uu___1 = lidents_of_term t1 in
      let uu___2 =
        let uu___3 = lidents_of_term t2 in
        let uu___4 = lidents_of_term t3 in FStarC_List.op_At uu___3 uu___4 in
      FStarC_List.op_At uu___1 uu___2
and lidents_of_pattern (p : FStarC_Parser_AST.pattern) :
  FStarC_Ident.lident Prims.list=
  match p.FStarC_Parser_AST.pat with
  | FStarC_Parser_AST.PatWild uu___ -> []
  | FStarC_Parser_AST.PatConst uu___ -> []
  | FStarC_Parser_AST.PatApp (p1, ps) ->
      let uu___ = lidents_of_pattern p1 in
      let uu___1 = (concat_map ()) lidents_of_pattern ps in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.PatVar (i, uu___, uu___1) ->
      let uu___2 = FStarC_Ident.lid_of_ids [i] in [uu___2]
  | FStarC_Parser_AST.PatName lid -> [lid]
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
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Parser_AST.PatOr ps -> (concat_map ()) lidents_of_pattern ps
  | FStarC_Parser_AST.PatOp uu___ -> []
  | FStarC_Parser_AST.PatVQuote t -> lidents_of_term t
  | FStarC_Parser_AST.PatRest -> []
and lidents_of_binder (b : FStarC_Parser_AST.binder) :
  FStarC_Ident.lident Prims.list=
  match b.FStarC_Parser_AST.b with
  | FStarC_Parser_AST.Annotated (uu___, t) -> lidents_of_term t
  | FStarC_Parser_AST.NoName t -> lidents_of_term t
  | uu___ -> []
let lidents_of_tycon_record
  (uu___ : ('uuuuu * 'uuuuu1 * 'uuuuu2 * FStarC_Parser_AST.term)) :
  FStarC_Ident.lident Prims.list=
  match uu___ with | (uu___1, uu___2, uu___3, t) -> lidents_of_term t
let lidents_of_constructor_payload
  (t : FStarC_Parser_AST.constructor_payload) :
  FStarC_Ident.lident Prims.list=
  match t with
  | FStarC_Parser_AST.VpOfNotation t1 -> lidents_of_term t1
  | FStarC_Parser_AST.VpArbitrary t1 -> lidents_of_term t1
  | FStarC_Parser_AST.VpRecord (tc, FStar_Pervasives_Native.None) ->
      (concat_map ()) lidents_of_tycon_record tc
  | FStarC_Parser_AST.VpRecord (tc, FStar_Pervasives_Native.Some t1) ->
      let uu___ = (concat_map ()) lidents_of_tycon_record tc in
      let uu___1 = lidents_of_term t1 in FStarC_List.op_At uu___ uu___1
let lidents_of_tycon_variant
  (tc :
    (FStarC_Ident.ident * FStarC_Parser_AST.constructor_payload
      FStar_Pervasives_Native.option * FStarC_Parser_AST.attributes_))
  : FStarC_Ident.lident Prims.list=
  match tc with
  | (uu___, FStar_Pervasives_Native.None, uu___1) -> []
  | (uu___, FStar_Pervasives_Native.Some t, uu___1) ->
      lidents_of_constructor_payload t
let lidents_of_tycon (tc : FStarC_Parser_AST.tycon) :
  FStarC_Ident.lident Prims.list=
  match tc with
  | FStarC_Parser_AST.TyconAbstract (uu___, bs, k) ->
      let uu___1 = (concat_map ()) lidents_of_binder bs in
      let uu___2 = opt_map lidents_of_term k in
      FStarC_List.op_At uu___1 uu___2
  | FStarC_Parser_AST.TyconAbbrev (uu___, bs, k, t) ->
      let uu___1 = (concat_map ()) lidents_of_binder bs in
      let uu___2 =
        let uu___3 = opt_map lidents_of_term k in
        let uu___4 = lidents_of_term t in FStarC_List.op_At uu___3 uu___4 in
      FStarC_List.op_At uu___1 uu___2
  | FStarC_Parser_AST.TyconRecord (uu___, bs, k, uu___1, tcs) ->
      let uu___2 = (concat_map ()) lidents_of_binder bs in
      let uu___3 =
        let uu___4 = opt_map lidents_of_term k in
        let uu___5 = (concat_map ()) lidents_of_tycon_record tcs in
        FStarC_List.op_At uu___4 uu___5 in
      FStarC_List.op_At uu___2 uu___3
  | FStarC_Parser_AST.TyconVariant (uu___, bs, k, tcs) ->
      let uu___1 = (concat_map ()) lidents_of_binder bs in
      let uu___2 =
        let uu___3 = opt_map lidents_of_term k in
        let uu___4 = (concat_map ()) lidents_of_tycon_variant tcs in
        FStarC_List.op_At uu___3 uu___4 in
      FStarC_List.op_At uu___1 uu___2
let lidents_of_lift (l : FStarC_Parser_AST.lift) :
  FStarC_Ident.lident Prims.list=
  let uu___ =
    match l.FStarC_Parser_AST.lift_op with
    | FStarC_Parser_AST.NonReifiableLift t -> lidents_of_term t
    | FStarC_Parser_AST.ReifiableLift (t1, t2) ->
        let uu___1 = lidents_of_term t1 in
        let uu___2 = lidents_of_term t2 in FStarC_List.op_At uu___1 uu___2
    | FStarC_Parser_AST.LiftForFree t -> lidents_of_term t in
  FStarC_List.op_At [l.FStarC_Parser_AST.msource; l.FStarC_Parser_AST.mdest]
    uu___
let rec lidents_of_decl (d : FStarC_Parser_AST.decl) :
  FStarC_Ident.lident Prims.list=
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
               FStarC_List.op_At uu___1 uu___2) lbs
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
        let uu___1 = let uu___2 = lidents_of_term t in l2 :: uu___2 in l1 ::
          uu___1 in
      l0 :: uu___
  | FStarC_Parser_AST.Polymonadic_subcomp (l0, l1, t) ->
      let uu___ = let uu___1 = lidents_of_term t in l1 :: uu___1 in l0 ::
        uu___
  | FStarC_Parser_AST.Pragma uu___ -> []
  | FStarC_Parser_AST.Assume (uu___, t) -> lidents_of_term t
  | FStarC_Parser_AST.Splice (uu___, uu___1, t) -> lidents_of_term t
  | FStarC_Parser_AST.DeclSyntaxExtension uu___ -> []
  | FStarC_Parser_AST.DeclToBeDesugared uu___ -> []
and lidents_of_effect_decl (ed : FStarC_Parser_AST.effect_decl) :
  FStarC_Ident.lident Prims.list=
  match ed with
  | FStarC_Parser_AST.DefineEffect (uu___, bs, t, ds) ->
      let uu___1 = (concat_map ()) lidents_of_binder bs in
      let uu___2 =
        let uu___3 = lidents_of_term t in
        let uu___4 = (concat_map ()) lidents_of_decl ds in
        FStarC_List.op_At uu___3 uu___4 in
      FStarC_List.op_At uu___1 uu___2
  | FStarC_Parser_AST.RedefineEffect (uu___, bs, t) ->
      let uu___1 = (concat_map ()) lidents_of_binder bs in
      let uu___2 = lidents_of_term t in FStarC_List.op_At uu___1 uu___2
type open_namespaces_and_abbreviations =
  {
  open_namespaces: FStarC_Ident.lident Prims.list ;
  module_abbreviations: (FStarC_Ident.ident * FStarC_Ident.lident) Prims.list }
let __proj__Mkopen_namespaces_and_abbreviations__item__open_namespaces
  (projectee : open_namespaces_and_abbreviations) :
  FStarC_Ident.lident Prims.list=
  match projectee with
  | { open_namespaces; module_abbreviations;_} -> open_namespaces
let __proj__Mkopen_namespaces_and_abbreviations__item__module_abbreviations
  (projectee : open_namespaces_and_abbreviations) :
  (FStarC_Ident.ident * FStarC_Ident.lident) Prims.list=
  match projectee with
  | { open_namespaces; module_abbreviations;_} -> module_abbreviations
type error_message =
  {
  message: FStar_Pprint.document Prims.list ;
  range: FStarC_Range_Type.t }
let __proj__Mkerror_message__item__message (projectee : error_message) :
  FStar_Pprint.document Prims.list=
  match projectee with | { message; range;_} -> message
let __proj__Mkerror_message__item__range (projectee : error_message) :
  FStarC_Range_Type.t= match projectee with | { message; range;_} -> range
type extension_parser =
  {
  parse_decl_name:
    Prims.string ->
      FStarC_Range_Type.t ->
        (error_message, FStarC_Ident.ident) FStar_Pervasives.either
    ;
  parse_decl:
    open_namespaces_and_abbreviations ->
      Prims.string ->
        FStarC_Range_Type.t ->
          (error_message, FStarC_Parser_AST.decl) FStar_Pervasives.either
    }
let __proj__Mkextension_parser__item__parse_decl_name
  (projectee : extension_parser) :
  Prims.string ->
    FStarC_Range_Type.t ->
      (error_message, FStarC_Ident.ident) FStar_Pervasives.either=
  match projectee with | { parse_decl_name; parse_decl;_} -> parse_decl_name
let __proj__Mkextension_parser__item__parse_decl
  (projectee : extension_parser) :
  open_namespaces_and_abbreviations ->
    Prims.string ->
      FStarC_Range_Type.t ->
        (error_message, FStarC_Parser_AST.decl) FStar_Pervasives.either=
  match projectee with | { parse_decl_name; parse_decl;_} -> parse_decl
let extension_parser_table : extension_parser FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int (20))
let register_extension_parser (ext : Prims.string)
  (parser : extension_parser) : unit=
  FStarC_SMap.add extension_parser_table ext parser
let lookup_extension_parser (ext : Prims.string) :
  extension_parser FStar_Pervasives_Native.option=
  let do1 uu___ = FStarC_SMap.try_find extension_parser_table ext in
  let uu___ = do1 () in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 = FStarC_Plugins.autoload_plugin ext in
      if uu___1 then do1 () else FStar_Pervasives_Native.None
  | r -> r
type extension_lang_parser =
  {
  parse_decls:
    Prims.string ->
      FStarC_Range_Type.t ->
        (error_message, FStarC_Parser_AST.decl Prims.list)
          FStar_Pervasives.either
    }
let __proj__Mkextension_lang_parser__item__parse_decls
  (projectee : extension_lang_parser) :
  Prims.string ->
    FStarC_Range_Type.t ->
      (error_message, FStarC_Parser_AST.decl Prims.list)
        FStar_Pervasives.either=
  match projectee with | { parse_decls;_} -> parse_decls
let as_open_namespaces_and_abbrevs (ls : FStarC_Parser_AST.decl Prims.list) :
  open_namespaces_and_abbreviations=
  FStarC_List.fold_right
    (fun d out ->
       match d.FStarC_Parser_AST.d with
       | FStarC_Parser_AST.Open (lid, uu___) ->
           {
             open_namespaces = (lid :: (out.open_namespaces));
             module_abbreviations = (out.module_abbreviations)
           }
       | FStarC_Parser_AST.ModuleAbbrev (i, lid) ->
           {
             open_namespaces = (out.open_namespaces);
             module_abbreviations = ((i, lid) :: (out.module_abbreviations))
           }
       | uu___ -> out) ls { open_namespaces = []; module_abbreviations = [] }
let extension_lang_parser_table : extension_lang_parser FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int (20))
let register_extension_lang_parser (ext : Prims.string)
  (parser : extension_lang_parser) : unit=
  FStarC_SMap.add extension_lang_parser_table ext parser
let lookup_extension_lang_parser (ext : Prims.string) :
  extension_lang_parser FStar_Pervasives_Native.option=
  let r = FStarC_SMap.try_find extension_lang_parser_table ext in
  match r with
  | FStar_Pervasives_Native.None ->
      let uu___ = FStarC_Plugins.autoload_plugin ext in
      if uu___
      then FStarC_SMap.try_find extension_lang_parser_table ext
      else FStar_Pervasives_Native.None
  | uu___ -> r
let parse_extension_lang (lang_name : Prims.string) (raw_text : Prims.string)
  (raw_text_pos : FStarC_Range_Type.range) :
  FStarC_Parser_AST.decl Prims.list=
  let extension_parser1 = lookup_extension_lang_parser lang_name in
  match extension_parser1 with
  | FStar_Pervasives_Native.None ->
      let uu___ =
        FStarC_Format.fmt1 "Unknown language extension %s" lang_name in
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
        raw_text_pos FStarC_Errors_Codes.Fatal_SyntaxError ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___)
  | FStar_Pervasives_Native.Some parser ->
      let uu___ = parser.parse_decls raw_text raw_text_pos in
      (match uu___ with
       | FStar_Pervasives.Inl error ->
           FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
             error.range FStarC_Errors_Codes.Fatal_SyntaxError ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic error.message)
       | FStar_Pervasives.Inr ds -> ds)
