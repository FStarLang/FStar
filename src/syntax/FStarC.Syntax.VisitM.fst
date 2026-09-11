module FStarC.Syntax.VisitM

open FStarC
open FStarC.Effect
open FStarC.List

open FStarC.Class.Monad

open FStarC.Syntax
open FStarC.Syntax.Syntax

type endo (m:Type -> Type) a = a -> ML (m a)

(* local visitor monad, this class is not exposed, it's just
a local shortcut. *)
class lvm (m:Type->Type) : Type = {
  lvm_monad       : monad m;

  f_term          : endo m term;
  f_binder        : endo m binder;
  f_binding_bv    : endo m bv;
  f_br            : endo m branch;
  f_comp          : endo m comp;
  f_residual_comp : endo m residual_comp;
  f_univ          : endo m universe;

  proc_quotes     : bool;
}

instance _lvm_monad (#m:_) (_ : lvm m) : Tot (monad m) = lvm_monad

let novfs (#m:Type->Type) {| monad m |} : lvm m = {
  lvm_monad       = FStar.Tactics.Typeclasses.solve;
  f_term          = return;
  f_binder        = return;
  f_binding_bv    = return;
  f_br            = return;
  f_comp          = return;
  f_residual_comp = return;
  f_univ          = return;

  proc_quotes     = false;
}

let f_aqual #m {|_ : lvm m|} aq : ML (m _) =
  let  {aqual_implicit=i; aqual_attributes=attrs} = aq in
  let! attrs = mapM f_term attrs in
  return {aqual_implicit=i; aqual_attributes=attrs}

let on_sub_arg #m {|_ : lvm m|} (a : arg) : ML (m arg) =
  let  (t, q) = a in
  let! t = t |> f_term in
  let! q = q |> map_optM f_aqual in
  return (t, q)

let on_sub_tscheme #m {| monad m |} {|_ : lvm m|}  (ts : tscheme) : ML (m tscheme) =
  let  (us, t) = ts in
  let! t = t |> f_term in // FIXME: push univs
  return (us, t)

(* Homeomorphic calls... for now *)
let f_arg            #m {|_ : lvm m|} : _ -> ML (m _) = on_sub_arg
let f_args           #m {|d : lvm m|} : _ -> ML (m _) = mapM (f_arg #m #d) // FIXME: why instantiate?
let f_tscheme        #m {|_ : lvm m|} : tscheme -> ML (m tscheme) = on_sub_tscheme

let on_sub_meta #m {| d : lvm m |} (md : metadata) : ML (m metadata) =
  match md with
  | Meta_pattern (pats, args) ->
    let! pats = pats |> mapM f_term in
    let! args = args |> mapM (f_args #m #d) in // FIXME: idem
    return <| Meta_pattern (pats, args)

  | Meta_monadic (m, typ) ->
    let! typ = typ |> f_term in
    return <| Meta_monadic (m, typ)

  | Meta_monadic_lift (m1, m2, typ) ->
    let! typ = typ |> f_term in
    return <| Meta_monadic_lift (m1, m2, typ)

  (* no subterms *)
  | Meta_named lid       -> return <| Meta_named lid
  | Meta_labeled (s,r,b) -> return <|Meta_labeled (s,r,b)
  | Meta_desugared i     -> return <| Meta_desugared i

let on_sub_letbinding #m {|lvm m|} (lb : letbinding) : ML (m letbinding) =
  let! lbname =
    match lb.lbname with
    | Inl bv -> Inl <$> f_binding_bv bv
    | Inr fv -> return (Inr fv)
  in
  let  lbunivs = lb.lbunivs in
  let! lbtyp = f_term lb.lbtyp in
  let  lbeff = lb.lbeff in
  let! lbattrs = mapM f_term lb.lbattrs in
  let  lbpos = lb.lbpos in
  let! lbdef = f_term lb.lbdef in // FIXME: push binder
  return <| { lbname; lbunivs; lbtyp; lbeff; lbattrs; lbpos; lbdef; }

let on_sub_ascription #m {| lvm m |} (a : ascription) : ML (m ascription) =
  let (tc, tacopt, b) = a in
  let! tc = match tc with
            | Inl t -> Inl <$> f_term t
            | Inr c -> Inr <$> f_comp c
  in
  let! tacopt = map_optM f_term tacopt in
  return (tc, tacopt, b)

(* Compress+unlazy *)
let rec compress (tm:term) : ML term =
  let tm = Subst.compress tm in
  match tm.n with
  (* unfold and retry *)
  | Tm_lazy li ->
    let tm' = Option.must !lazy_chooser li.lkind li in
    compress tm'

  | _ -> tm

(* Not recursive itself! This does not apply anything deeply! The
recursion on deep subterms comes from the knot being tied below. *)
let on_sub_term #m {|d : lvm m |} (tm : term) : ML (m term) =
  let mk t = Syntax.mk t tm.pos in
  let tm = compress tm in
  match tm.n with
  | Tm_lazy _
  | Tm_delayed _ ->
    failwith "impos"

  (* no subterms *)
  | Tm_fvar _
  | Tm_constant _
  | Tm_unknown
  | Tm_bvar _
  | Tm_name _
  | Tm_uvar _ ->
    return tm

  | Tm_uinst (f, us) ->
    let! f = f_term f in
    let! us = mapM f_univ us in
    return <| mk (Tm_uinst (f, us))

  | Tm_type u ->
    let! u = u |> f_univ in
    return <| mk (Tm_type u)

  | Tm_app {hd; arg} ->
    let! hd    = f_term hd in
    let! arg   = f_arg #m #d arg in
    return <| mk (Tm_app {hd; arg})

  | Tm_abs {b; body=t; rc_opt} ->
    let! b      = f_binder b in
    let! t      = f_term t in
    let! rc_opt = map_optM f_residual_comp rc_opt in
    return <| mk (Tm_abs {b; body=t; rc_opt})

  | Tm_arrow {b; comp=c} ->
    let! b     = f_binder b in
    let! c     = f_comp c in
    return <| mk (Tm_arrow {b; comp=c})

  | Tm_refine {b=bv; phi} ->
    let! bv    = f_binding_bv bv in
    let! phi   = f_term phi in
    return <| mk (Tm_refine {b=bv; phi})

  | Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt} ->
    let! sc      = f_term sc in
    let! asc_opt = asc_opt |> map_optM (fun (b, asc) -> Mktuple2 <$> f_binder b <*> on_sub_ascription asc <: ML (m _)) in
    let! brs     = mapM f_br brs in
    let! rc_opt  = rc_opt |> map_optM f_residual_comp in
    return <| mk (Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt})

  | Tm_ascribed {tm=e; asc=a; eff_opt=lopt} ->
    let! e = f_term e in
    let! a = a |> on_sub_ascription in
    return <| mk (Tm_ascribed {tm=e; asc=a; eff_opt=lopt})

  | Tm_let {lbs=(is_rec, lbs); body=t} ->
    let! lbs = lbs |> mapM on_sub_letbinding in
    let! t = t |> f_term in
    return <| mk (Tm_let {lbs=(is_rec, lbs); body=t})

  | Tm_quoted (qtm, qi) ->
    if d.proc_quotes || qi.qkind = Quote_dynamic then
      let! qtm = qtm |> f_term in
      // let! qi = Syntax.on_antiquoted (f_term vfs) qi in
      // FIXME ^ no monadic variant
      return <| mk (Tm_quoted (qtm, qi))
    else
      return tm

  | Tm_meta {tm=t; meta=md} ->
    let! t   = t |> f_term in
    let! md  = md |> on_sub_meta in
    return <| mk (Tm_meta {tm=t; meta=md})

let on_sub_binding_bv #m {|d : lvm m |} (x : bv) : ML (m bv) =
  let! sort = x.sort |> f_term in
  return { x with sort = sort }

let on_sub_binder #m {|d : lvm m |} (b : binder) : ML (m binder) =
  let! binder_bv = b.binder_bv |> f_binding_bv in
  let! binder_qual = b.binder_qual |> map_optM (function Meta t -> Meta <$> f_term t
                                                       | q -> return q) in
  let binder_positivity = b.binder_positivity in
  let! binder_attrs = b.binder_attrs |> mapM f_term in
  return <| {
    binder_bv;
    binder_qual;
    binder_positivity;
    binder_attrs;
  }

let rec on_sub_pat #m {|d : lvm m |} (p0 : pat) : ML (m pat) =
  let mk p = { v=p; p=p0.p } in
  match p0.v with
  | Pat_constant _ ->
    return p0

  | Pat_cons (fv, us, subpats) ->
    let! us = us |> map_optM (mapM #m f_univ) in
    let! subpats = subpats |> mapM (fun (p, b) -> Mktuple2 <$> on_sub_pat p <*> return b <: ML (m _)) in
    return <| mk (Pat_cons (fv, us, subpats))

  | Pat_var bv ->
    let! bv = bv |> f_binding_bv in
    return <| mk (Pat_var bv)

  | Pat_dot_term t ->
    let! t = t |> map_optM f_term in
    return <| mk (Pat_dot_term t)

let on_sub_br #m {|d : lvm m |} br : ML (m _) =
  let  (pat, wopt, body) = br in
  let! pat = pat |> on_sub_pat in
  let! wopt = wopt |> map_optM f_term in
  let! body = body |> f_term in
  return (pat, wopt, body)

let __on_decreases #m {|d : lvm m |} (f : term -> ML (m term)) (cf : cflag) : ML (m cflag) =
  match cf with
  | SMTPAT p                         -> SMTPAT <$> f p
  | DECREASES (Decreases_lex l)      -> DECREASES <$> (Decreases_lex <$> mapM f l)
  | DECREASES (Decreases_wf (r, t))  -> DECREASES <$> (Decreases_wf <$> (Mktuple2 <$> f r <*>  f t))
  | f -> return f

let on_sub_comp_typ #m {|d : lvm m |} ct : ML (m _) =
  let  effect_name = ct.effect_name in
  let  source_effect_name = ct.source_effect_name in
  let! result_typ = ct.result_typ |> f_term in
  let! flags = ct.flags |> mapM (__on_decreases #m #d f_term) in
  return <| {
    effect_name;
    result_typ;
    flags;
    source_effect_name;
  }

let on_sub_comp #m {|d : lvm m |} c : ML (m comp) =
  let! cn =
    match c.n with
    | Comp ct -> Comp <$> on_sub_comp_typ ct
  in
  return <| Syntax.mk cn c.pos

let on_sub_residual_comp #m {|d : lvm m |} (rc : residual_comp) : ML (m residual_comp) =
  let  residual_effect = rc.residual_effect in
  let! residual_typ = rc.residual_typ |> map_optM f_term in
  let! residual_flags = rc.residual_flags |> mapM (__on_decreases #m #d f_term) in
  // ^ review: residual flags should not have terms
  return <| {
    residual_effect;
    residual_typ;
    residual_flags;
  }

let on_sub_univ #m {|d : lvm m |} (u : universe) : ML (m universe) =
  let u = Subst.compress_univ u in
  match u with
  | U_max us ->
    U_max <$> mapM f_univ us
  | U_succ u ->
    U_succ <$> f_univ u

  | U_zero
  | U_bvar _
  | U_name _
  | U_unknown
  | U_unif _ ->
    return u

let mapTuple2 #m {| monad m |} (f : 'a -> ML (m 'b)) (g : 'c -> ML (m 'd)) (t : 'a & 'c) : ML (m ('b & 'd)) =
  Mktuple2 <$> f t._1 <*> g t._2

let rec on_sub_sigelt' #m {|d : lvm m |} (se : sigelt') : ML (m sigelt') =
  match se with
  | Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params } ->
    let! params = params |> mapM f_binder in
    let! t = t |> f_term in
    return <| Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params }

  | Sig_bundle {ses; lids} ->
    let! ses = ses |> mapM on_sub_sigelt in
    return <| Sig_bundle {ses; lids}

  | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params; proj_disc_lids} ->
    let! t = t |> f_term in
    return <| Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params; proj_disc_lids }

  | Sig_declare_typ {lid; us; t} ->
    let! t = t |> f_term in
    return <| Sig_declare_typ {lid; us; t}

  | Sig_let {lbs=(is_rec, lbs); lids} ->
    let! lbs = lbs |> mapM on_sub_letbinding in
    return <| Sig_let {lbs=(is_rec, lbs); lids}

  | Sig_assume {lid; us; phi} ->
    let! phi = phi |> f_term in
    return <| Sig_assume {lid; us; phi}

  | Sig_new_effect ed ->
    let  mname           = ed.mname in
    let  cattributes     = ed.cattributes in
    let! combinators =
      match ed.combinators with
      | None -> return None
      | Some c ->
        let! repr        = c.repr        |> f_tscheme in
        let! return_repr = c.return_repr |> f_tscheme in
        let! bind_repr   = c.bind_repr   |> f_tscheme in
        let! repr_universe = c.repr_universe |> f_tscheme in
        return (Some { repr; return_repr; bind_repr; repr_universe })
    in
    let! eff_attrs       = ed.eff_attrs |> mapM f_term in
    let  extraction_mode = ed.extraction_mode in
    let ed = { mname; cattributes; combinators; eff_attrs; extraction_mode; } in
    return <| Sig_new_effect ed

  | Sig_sub_effect se ->
    let! lift =
      match se.lift with
      | None -> return None
      | Some ts -> let! ts = ts |> f_tscheme in return (Some ts)
    in
    return <| Sig_sub_effect { se with lift }

  (* An effect abbreviation is a pair of names: no subterms to visit. *)
  | Sig_effect_abbrev _ ->
    return se

  (* No content, except for Check. *)
  | Sig_pragma (Check t) ->
    let! t = f_term t in
    return <| Sig_pragma (Check t)
  | Sig_pragma (Eval t) ->
    let! t = f_term t in
    return <| Sig_pragma (Eval t)
  | Sig_pragma _ -> return se

  (* These two below are hardly used, since they disappear after
  typechecking, but are still useful so the desugarer can make use of
  deep_compress_se. *)
  | Sig_fail {rng; errs; fail_in_lax; ses} ->
    let! ses = ses |> mapM on_sub_sigelt in
    return <| Sig_fail {rng; errs; fail_in_lax; ses}

  | Sig_splice {is_typed; lids; tac} ->
    let! tac = tac |> f_term in
    return <| Sig_splice {is_typed; lids; tac}

  | _ -> failwith "on_sub_sigelt: missing case"

and on_sub_sigelt #m {|d : lvm m |} (se : sigelt) : ML (m sigelt) =
  let! sigel    = se.sigel |> on_sub_sigelt' in
  let  sigrng   = se.sigrng in
  let  sigquals = se.sigquals in
  let  sigmeta  = se.sigmeta in
  let! sigattrs = se.sigattrs |> mapM f_term in
  let  sigopts  = se.sigopts in
  let  sigopens_and_abbrevs = se.sigopens_and_abbrevs in
  return <| { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts; sigopens_and_abbrevs; }

let (>>=) (#m:_) {|monad m|} #a #b (c : m a) (f : a -> ML (m b)) : ML (m b) =
  let! x = c in f x

let (<<|) (#m:_) {|monad m|} #a #b (f : a -> ML (m b)) (c : m a) : ML (m b) =
  let! x = c in f x

// Bottom up. The record is a reference so it can be easily cyclic.
let tie_bu (#m : Type -> Type) {| md : monad m |} (d : lvm m) : ML (lvm m) =
  // needs explicit eta to not loop?
  let r : ref (lvm m) = mk_ref (novfs #m #md) in // FIXME implicits
  r :=
    {
      lvm_monad       = (!r).lvm_monad;

      f_term          = (fun x -> f_term          #_ #d <<| on_sub_term          #_ #!r x);
      f_binding_bv    = (fun x -> f_binding_bv    #_ #d <<| on_sub_binding_bv    #_ #!r x);
      f_binder        = (fun x -> f_binder        #_ #d <<| on_sub_binder        #_ #!r x);
      f_br            = (fun x -> f_br            #_ #d <<| on_sub_br            #_ #!r x);
      f_comp          = (fun x -> f_comp          #_ #d <<| on_sub_comp          #_ #!r x);
      f_residual_comp = (fun x -> f_residual_comp #_ #d <<| on_sub_residual_comp #_ #!r x);
      f_univ          = (fun x -> f_univ          #_ #d <<| on_sub_univ          #_ #!r x);

      proc_quotes     = d.proc_quotes;
    };
  !r

let visitM_term_univs #m {| md : monad m |} (proc_quotes : bool) vt vu (tm : term) : ML (m term) =
  let dict : lvm m =
    tie_bu #m #md { novfs #m #md with f_term = vt; f_univ = vu; proc_quotes = proc_quotes }
  in
  f_term #_ #dict tm

let visitM_term #m {| md : monad m |} (proc_quotes : bool) vt (tm : term) : ML (m term) =
  visitM_term_univs true vt return tm

let visitM_sigelt #m {| md : monad m |} (proc_quotes : bool) vt vu (tm : sigelt) : ML (m sigelt) =
  let dict : lvm m =
    tie_bu #m #md { novfs #m #md with f_term = vt; f_univ = vu; proc_quotes = proc_quotes }
  in
  on_sub_sigelt #_ #dict tm


(* Example: compute all lidents appearing in a sigelt:

let open FStarC.Class.Show in
let open FStarC.Class.Monad in
let open FStarC.Writer in

type mymon = writer (list lident)

let m = VisitM.visitM_sigelt
         (fun t -> (match t.n with
                   | Tm_fvar fv -> Writer.emit [lid_of_fv fv]
                   | _ -> return ());!
                     return t)
                     (fun #a b c -> c) se
in
let lids, _ = Writer.run_writer m in
Format.print1 "Lids = %s\n" (show lids);

*)
