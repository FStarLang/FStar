module FStarC.Parser.AST.VisitM

open FStarC
open FStarC.Effect
open FStarC.Parser.AST
open FStarC.Class.Monad
module AST = FStarC.Parser.AST

let nops #m {| monad m |} : dict m = {
    f_term'                    = return;
    f_term                     = return;
    f_match_returns_annotation = return;
    f_patterns                 = return;
    f_calc_step                = return;
    f_attributes_              = return;
    f_binder'                  = return;
    f_binder                   = return;
    f_pattern'                 = return;
    f_pattern                  = return;
    f_branch                   = return;
    f_arg_qualifier            = return;
    f_aqual                    = return;
    f_imp                      = return;
  }

(* Apply a monadic function on every (immediate) subcomponent. *)
let on_sub_term'
  #m {| monad m |} (d : dict m)
  (t : term') : m term'
=
  match t with
  (* No subterms *)
  | Wild
  | Const _
  | Uvar _
  | Var _
  | Name _
  | Projector _
     -> return t
  | Op (op, ts) ->
    let! ts = mapM d.f_term ts in
    return <| Op (op, ts)
  | Construct (c, args) ->
    let! args = mapM (fun (t, imp) -> d.f_term t >>= fun t' -> return (t', imp)) args in
    return <| Construct (c, args)
  | Abs (ps, t) ->
    let! ps = mapM d.f_pattern ps in
    let! t = d.f_term t in
    return <| Abs (ps, t)
  | Function (bs, r) ->
    let! bs = mapM d.f_branch bs in
    return <| Function (bs, r)
  | App (ff, a, imp) ->
    let! ff = d.f_term ff in
    let! a = d.f_term a in
    let! imp = d.f_imp imp in
    return <| App (ff, a, imp)
  | Let (rec_flag, bs, t) ->
    let! bs = mapM (fun (attrs, (p, t)) ->
      let! attrs = map_optM d.f_attributes_ attrs in
      let! p = d.f_pattern p in
      let! t = d.f_term t in
      return (attrs, (p, t))
    ) bs in
    let! t = d.f_term t in
    return <| Let (rec_flag, bs, t)
  | LetOperator (bs, t) ->
    let! bs = mapM (fun (i, p, t) ->
      let! p = d.f_pattern p in
      let! t = d.f_term t in
      return (i, p, t)
    ) bs in
    let! t = d.f_term t in
    return <| LetOperator (bs, t)
  | LetOpen (m, t) ->
    let! t = d.f_term t in
    return <| LetOpen (m, t)
  | LetOpenRecord (t1, t2, t3) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    let! t3 = d.f_term t3 in
    return <| LetOpenRecord (t1, t2, t3)
  | Seq (t1, t2) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    return <| Seq (t1, t2)
  | Bind (p, t1, t2) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    return <| Bind (p, t1, t2)
  | If (cond, iopt, aopt, then_branch, else_branch) ->
    let! cond = d.f_term cond in
    let! aopt = map_optM d.f_match_returns_annotation aopt in
    let! then_branch = d.f_term then_branch in
    let! else_branch = d.f_term else_branch in
    return <| If (cond, iopt, aopt, then_branch, else_branch)
  | Match (scrutinee, iopt, aopt, branches) ->
    let! scrutinee = d.f_term scrutinee in
    let! aopt = map_optM d.f_match_returns_annotation aopt in
    let! branches = mapM d.f_branch branches in
    return <| Match (scrutinee, iopt, aopt, branches)
  | TryWith (scrutinee, branches) ->
    let! scrutinee = d.f_term scrutinee in
    let! branches = mapM d.f_branch branches in
    return <| TryWith (scrutinee, branches)
  | Ascribed (e, t, tac_opt, eq) ->
    let! e = d.f_term e in
    let! t = d.f_term t in
    let! tac_opt = map_optM d.f_term tac_opt in
    return <| Ascribed (e, t, tac_opt, eq)
  | Record (bopt, flds) ->
    let! bopt = map_optM d.f_term bopt in
    let! flds = mapM (fun (nm, e) ->
      let! e = d.f_term e in
      return (nm, e)
    ) flds in
    return <| Record (bopt, flds)
  | Project (e, nm) ->
    let! e = d.f_term e in
    return <| Project (e, nm)
  | Product (bs, t) ->
    let! bs = mapM d.f_binder bs in
    let! t = d.f_term t in
    return <| Product (bs, t)
  | Sum (bs, t) ->
    let! bs = mapM (function Inl b -> Inl <$> d.f_binder b | Inr t -> Inr <$> d.f_term t) bs in
    let! t = d.f_term t in
    return <| Sum (bs, t)
  | QForall (bs, pats, t) ->
    let! bs = mapM d.f_binder bs in
    let! pats = d.f_patterns pats in
    let! t = d.f_term t in
    return <| QForall (bs, pats, t)
  | QExists (bs, pats, t) ->
    let! bs = mapM d.f_binder bs in
    let! pats = d.f_patterns pats in
    let! t = d.f_term t in
    return <| QExists (bs, pats, t)
  | QuantOp (id, bs, pats, t) ->
    let! bs = mapM d.f_binder bs in
    let! pats = d.f_patterns pats in
    let! t = d.f_term t in
    return <| QuantOp (id, bs, pats, t)
  | Refine (b, t) ->
    let! b = d.f_binder b in
    let! t = d.f_term t in
    return <| Refine (b, t)
  | NamedTyp (i, t) ->
    let! t = d.f_term t in
    return <| NamedTyp (i, t)
  | Paren t ->
    let! t = d.f_term t in
    return <| Paren t
  | Requires t ->
    let! t = d.f_term t in
    return <| Requires t
  | Ensures t ->
    let! t = d.f_term t in
    return <| Ensures t
  | LexList ts ->
    let! ts = mapM d.f_term ts in
    return <| LexList ts
  | WFOrder (t1, t2) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    return <| WFOrder (t1, t2)
  | Decreases t ->
    let! t = d.f_term t in
    return <| Decreases t
  | Labeled (t, lbl, b) ->
    let! t = d.f_term t in
    return <| Labeled (t, lbl, b)
  | Discrim l ->
    return <| Discrim l
  | Attributes ts ->
    let! ts = mapM d.f_term ts in
    return <| Attributes ts
  | Antiquote t ->
    let! t = d.f_term t in
    return <| Antiquote t
  | Quote (t, k) ->
    let! t = d.f_term t in
    return <| Quote (t, k)
  | VQuote t ->
    let! t = d.f_term t in
    return <| VQuote t
  | CalcProof (rel, init, steps) ->
    let! rel = d.f_term rel in
    let! init = d.f_term init in
    let! steps = mapM d.f_calc_step steps in
    return <| CalcProof (rel, init, steps)
  | IntroForall (bs, t1, t2) ->
    let! bs = mapM d.f_binder bs in
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    return <| IntroForall (bs, t1, t2)
  | IntroExists (bs, t1, ts, t3) ->
    let! bs = mapM d.f_binder bs in
    let! t1 = d.f_term t1 in
    let! ts = mapM d.f_term ts in
    let! t3 = d.f_term t3 in
    return <| IntroExists (bs, t1, ts, t3)
  | IntroImplies (t1, t2, b, t3) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    let! b = d.f_binder b in
    let! t3 = d.f_term t3 in
    return <| IntroImplies (t1, t2, b, t3)
  | IntroOr (b, t1, t2, t3) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    let! t3 = d.f_term t3 in
    return <| IntroOr (b, t1, t2, t3)
  | IntroAnd (t1, t2, t3, t4) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    let! t3 = d.f_term t3 in
    let! t4 = d.f_term t4 in
    return <| IntroAnd (t1, t2, t3, t4)
  | ElimForall (bs, t, ts) ->
    let! bs = mapM d.f_binder bs in
    let! t = d.f_term t in
    let! ts = mapM d.f_term ts in
    return <| ElimForall (bs, t, ts)
  | ElimExists (bs, t1, t2, b, t3) ->
    let! bs = mapM d.f_binder bs in
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    let! b = d.f_binder b in
    let! t3 = d.f_term t3 in
    return <| ElimExists (bs, t1, t2, b, t3)
  | ElimImplies (t1, t2, t3) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    let! t3 = d.f_term t3 in
    return <| ElimImplies (t1, t2, t3)
  | ElimOr (t1, t2, t3, b1, p1, b2, p2) ->
    let! t1 = d.f_term t1 in
    let! t2 = d.f_term t2 in
    let! t3 = d.f_term t3 in
    let! b1 = d.f_binder b1 in
    let! p1 = d.f_term p1 in
    let! b2 = d.f_binder b2 in
    let! p2 = d.f_term p2 in
    return <| ElimOr (t1, t2, t3, b1, p1, b2, p2)
  | ElimAnd (p, q, r, b1, b2, pf) ->
    let! p = d.f_term p in
    let! q = d.f_term q in
    let! r = d.f_term r in
    let! b1 = d.f_binder b1 in
    let! b2 = d.f_binder b2 in
    let! pf = d.f_term pf in
    return <| ElimAnd (p, q, r, b1, b2, pf)
  | ListLiteral ts ->
    let! ts = mapM d.f_term ts in
    return <| ListLiteral ts
  | SeqLiteral ts ->
    let! ts = mapM d.f_term ts in
    return <| SeqLiteral ts

let on_sub_term #m {| monad m |} (d : dict m) (t : term) : m term =
  let {tm; range; level} = t in
  let! tm = d.f_term' tm in
  return {tm; range; level}

let on_sub_match_returns_annotation
  #m {| monad m |} (d : dict m) (x : match_returns_annotation) : m match_returns_annotation =
  let (iopt, t, b) = x in
  let! t = d.f_term t in
  return (iopt, t, b)

let on_sub_patterns
  #m {| monad m |} (d : dict m)
  (x : patterns) : m patterns
=
  let (ids, tss) = x in
  let! tss = mapM (mapM d.f_term) tss in
  return (ids, tss)

let on_sub_calc_step
  #m {| monad m |} (d : dict m)
  (x : calc_step) : m calc_step
=
  match x with
  | CalcStep (rel, pf, e') ->
    let! rel = d.f_term rel in
    let! pf = d.f_term pf in
    let! e' = d.f_term e' in
    return <| CalcStep (rel, pf, e')

let on_sub_attributes_
  #m {| monad m |} (d : dict m)
  (x : attributes_) : m attributes_
=
  let ts = x in
  let! ts = mapM d.f_term ts in
  return ts

let on_sub_binder'
  #m {| monad m |} (d : dict m)
  (x : binder') : m binder'
=
  match x with
  | Variable i ->
    return <| Variable i
  | Annotated (i, t) ->
    let! t = d.f_term t in
    return <| Annotated (i, t)
  | NoName t ->
    let! t = d.f_term t in
    return <| NoName t

let on_sub_binder
  #m {| monad m |} (d : dict m)
  (x : binder) : m binder
=
  let {b; brange; blevel; aqual; battributes} = x in
  let! b = d.f_binder' b in
  let! aqual = d.f_aqual aqual in
  let! battributes = mapM d.f_term battributes in
  return {b; brange; blevel; aqual; battributes}

let on_sub_pattern'
  #m {| monad m |} (d : dict m)
  (x : pattern') : m pattern'
=
  match x with
  | PatWild (aq, attrs) ->
    let! aq = d.f_aqual aq in
    let! attrs = d.f_attributes_ attrs in
    return <| PatWild (aq, attrs)
  | PatConst c ->
    return <| PatConst c
  | PatApp (p, ps) ->
    let! p = d.f_pattern p in
    let! ps = mapM d.f_pattern ps in
    return <| PatApp (p, ps)
  | PatVar (i, aq, attrs) ->
    let! aq = d.f_aqual aq in
    let! attrs = d.f_attributes_ attrs in
    return <| PatVar (i, aq, attrs)
  | PatName l ->
    return <| PatName l
  | PatList ps ->
    let! ps = mapM d.f_pattern ps in
    return <| PatList ps
  | PatRest ->
    return <| PatRest
  | PatTuple (ps, b) ->
    let! ps = mapM d.f_pattern ps in
    return <| PatTuple (ps, b)
  | PatRecord ps ->
    let! ps = mapM (fun (l, p) -> d.f_pattern p >>= fun p -> return (l, p)) ps in
    return <| PatRecord ps
  | PatAscribed (p, (t, tacopt)) ->
    let! p = d.f_pattern p in
    let! t = d.f_term t in
    let! tacopt = map_optM d.f_term tacopt in
    return <| PatAscribed (p, (t, tacopt))
  | PatOr ps ->
    let! ps = mapM d.f_pattern ps in
    return <| PatOr ps
  | PatOp i ->
    return <| PatOp i
  | PatVQuote t ->
    let! t = d.f_term t in
    return <| PatVQuote t

let on_sub_pattern
  #m {| monad m |} (d : dict m)
  (x : pattern) : m pattern
=
  let {pat; prange} = x in
  let! pat = d.f_pattern' pat in
  return {pat; prange}

let on_sub_branch
  #m {| monad m |} (d : dict m)
  (x : branch) : m branch
=
  let (pat, wopt, t) = x in
  let! pat = on_sub_pattern d pat in
  let! wopt = map_optM d.f_term wopt in
  let! t = d.f_term t in
  return (pat, wopt, t)

let on_sub_arg_qualifier
  #m {| monad m |} (d : dict m)
  (x : arg_qualifier) : m arg_qualifier
=
  match x with
  | Implicit
  | Equality
  | TypeClassArg -> return x
  | Meta t ->
    let! t = d.f_term t in
    return <| Meta t

let on_sub_aqual
  #m {| monad m |} (d : dict m)
  (x : aqual) : m aqual
=
  map_optM d.f_arg_qualifier x

let on_sub_imp
  #m {| monad m |} (d : dict m)
  (x : imp) : m imp
=
  match x with
  | FsTypApp
  | Hash
  | UnivApp
  | Infix
  | Nothing ->
    return x
  | HashBrace t ->
    let! t = d.f_term t in
    return <| HashBrace t


let tie #m {| monad m |} (pre post : dict m) : dict m =
  let r : ref (dict m) = mk_ref (nops #m #_) in
  let th #m (f : dict m -> 'a -> 'b) (r : ref (dict m)) : 'a -> 'b =
    fun x -> f (!r) x
  in
   (* Note: we need to thunk the access to r. *)
  r := {
   f_term'                     =  pre.f_term'                     >=> th on_sub_term' r                    >=> post.f_term'                   ;
   f_term                      =  pre.f_term                      >=> th on_sub_term r                     >=> post.f_term                    ;
   f_match_returns_annotation  =  pre.f_match_returns_annotation  >=> th on_sub_match_returns_annotation r >=> post.f_match_returns_annotation;
   f_patterns                  =  pre.f_patterns                  >=> th on_sub_patterns r                 >=> post.f_patterns                ;
   f_calc_step                 =  pre.f_calc_step                 >=> th on_sub_calc_step r                >=> post.f_calc_step               ;
   f_attributes_               =  pre.f_attributes_               >=> th on_sub_attributes_ r              >=> post.f_attributes_             ;
   f_binder'                   =  pre.f_binder'                   >=> th on_sub_binder' r                  >=> post.f_binder'                 ;
   f_binder                    =  pre.f_binder                    >=> th on_sub_binder r                   >=> post.f_binder                  ;
   f_pattern'                  =  pre.f_pattern'                  >=> th on_sub_pattern' r                 >=> post.f_pattern'                ;
   f_pattern                   =  pre.f_pattern                   >=> th on_sub_pattern r                  >=> post.f_pattern                 ;
   f_branch                    =  pre.f_branch                    >=> th on_sub_branch r                   >=> post.f_branch                  ;
   f_arg_qualifier             =  pre.f_arg_qualifier             >=> th on_sub_arg_qualifier r            >=> post.f_arg_qualifier           ;
   f_aqual                     =  pre.f_aqual                     >=> th on_sub_aqual r                    >=> post.f_aqual                   ;
   f_imp                       =  pre.f_imp                       >=> th on_sub_imp r                      >=> post.f_imp                     ;
  };
  !r

let tie_bu #m {| monad m |} (d : dict m) : dict m = tie d (nops #_ #_)
let tie_td #m {| monad m |} (d : dict m) : dict m = tie (nops #_ #_) d
