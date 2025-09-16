module FStarC.Syntax.VisitM

open FStarC
open FStarC.Effect
open FStarC.List

open FStarC.Class.Monad

open FStarC.Syntax
open FStarC.Syntax.Syntax

type endo (m:Type -> Type) a = a -> m a

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

let f_aqual #m {|_ : lvm m|} aq : m _ =
  let  {aqual_implicit=i; aqual_attributes=attrs} = aq in
  let! attrs = mapM f_term attrs in
  return {aqual_implicit=i; aqual_attributes=attrs}

let on_sub_arg #m {|_ : lvm m|} (a : arg) : m arg =
  let  (t, q) = a in
  let! t = t |> f_term in
  let! q = q |> map_optM f_aqual in
  return (t, q)

let on_sub_tscheme #m {| monad m |} {|_ : lvm m|}  (ts : tscheme) : m tscheme =
  let  (us, t) = ts in
  let! t = t |> f_term in // FIXME: push univs
  return (us, t)

(* Homeomorphic calls... for now *)
let f_arg            #m {|_ : lvm m|} : _ -> m _ = on_sub_arg
let f_args           #m {|d : lvm m|} : _ -> m _ = mapM (f_arg #m #d) // FIXME: why instantiate?
let f_tscheme        #m {|_ : lvm m|} : tscheme -> m tscheme = on_sub_tscheme

let on_sub_meta #m {| d : lvm m |} (md : metadata) : m metadata =
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

let on_sub_letbinding #m {|lvm m|} (lb : letbinding) : m letbinding =
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

let on_sub_ascription #m {| lvm m |} (a : ascription) : m ascription =
  let (tc, tacopt, b) = a in
  let! tc = match tc with
            | Inl t -> Inl <$> f_term t
            | Inr c -> Inr <$> f_comp c
  in
  let! tacopt = map_optM f_term tacopt in
  return (tc, tacopt, b)

(* Compress+unlazy *)
let rec compress (tm:term) : term =
  let tm = Subst.compress tm in
  match tm.n with
  (* unfold and retry *)
  | Tm_lazy li ->
    let tm' = Option.must !lazy_chooser li.lkind li in
    compress tm'

  | _ -> tm

(* Not recursive itself! This does not apply anything deeply! The
recursion on deep subterms comes from the knot being tied below. *)
let on_sub_term #m {|d : lvm m |} (tm : term) : m term =
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

  | Tm_app {hd; args} ->
    let! hd    = f_term hd in
    let! args  = mapM (f_arg #m #d) args in
    return <| mk (Tm_app {hd; args})

  | Tm_abs {bs; body=t; rc_opt} ->
    let! bs     = mapM f_binder bs in
    let! t      = f_term t in
    let! rc_opt = map_optM f_residual_comp rc_opt in
    return <| mk (Tm_abs {bs; body=t; rc_opt})

  | Tm_arrow {bs; comp=c} ->
    let! bs    = mapM f_binder bs in
    let! c     = f_comp c in
    return <| mk (Tm_arrow {bs; comp=c})

  | Tm_refine {b=bv; phi} ->
    let! bv    = f_binding_bv bv in
    let! phi   = f_term phi in
    return <| mk (Tm_refine {b=bv; phi})

  | Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt} ->
    let! sc      = f_term sc in
    let! asc_opt = asc_opt |> map_optM (fun (b, asc) -> Mktuple2 <$> f_binder b <*> on_sub_ascription asc <: m _) in
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

let on_sub_binding_bv #m {|d : lvm m |} (x : bv) : m bv =
  let! sort = x.sort |> f_term in
  return { x with sort = sort }

let on_sub_binder #m {|d : lvm m |} (b : binder) : m binder =
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

let rec on_sub_pat #m {|d : lvm m |} (p0 : pat) : m pat =
  let mk p = { v=p; p=p0.p } in
  match p0.v with
  | Pat_constant _ ->
    return p0

  | Pat_cons (fv, us, subpats) ->
    let! us = us |> map_optM (mapM #m f_univ) in
    let! subpats = subpats |> mapM (fun (p, b) -> Mktuple2 <$> on_sub_pat p <*> return b <: m _) in
    return <| mk (Pat_cons (fv, us, subpats))

  | Pat_var bv ->
    let! bv = bv |> f_binding_bv in
    return <| mk (Pat_var bv)

  | Pat_dot_term t ->
    let! t = t |> map_optM f_term in
    return <| mk (Pat_dot_term t)

let on_sub_br #m {|d : lvm m |} br : m _ =
  let  (pat, wopt, body) = br in
  let! pat = pat |> on_sub_pat in
  let! wopt = wopt |> map_optM f_term in
  let! body = body |> f_term in
  return (pat, wopt, body)

let on_sub_comp_typ #m {|d : lvm m |} ct : m _ =
  let! comp_univs = ct.comp_univs |> mapM f_univ in
  let  effect_name = ct.effect_name in
  let! result_typ = ct.result_typ |> f_term in
  let! effect_args = ct.effect_args |> mapM (f_arg #m #d) in
  let  flags = ct.flags in
  return <| {
    comp_univs;
    effect_name;
    result_typ;
    effect_args;
    flags;
  }

let on_sub_comp #m {|d : lvm m |} c : m comp =
  let! cn =
    match c.n with
    | Total typ  -> Total <$> f_term typ
    | GTotal typ -> GTotal <$> f_term typ
    | Comp ct -> Comp <$> on_sub_comp_typ ct
  in
  return <| Syntax.mk cn c.pos

let __on_decreases #m {|d : lvm m |} f : cflag -> m cflag = function
  | DECREASES (Decreases_lex l)      -> DECREASES <$> (Decreases_lex <$> mapM f l)
  | DECREASES (Decreases_wf (r, t))  -> DECREASES <$> (Decreases_wf <$> (Mktuple2 <$> f r <*>  f t))
  | f -> return f

let on_sub_residual_comp #m {|d : lvm m |} (rc : residual_comp) : m residual_comp =
  let  residual_effect = rc.residual_effect in
  let! residual_typ = rc.residual_typ |> map_optM f_term in
  let! residual_flags = rc.residual_flags |> mapM (__on_decreases f_term) in
  // ^ review: residual flags should not have terms
  return <| {
    residual_effect;
    residual_typ;
    residual_flags;
  }

let on_sub_univ #m {|d : lvm m |} (u : universe) : m universe =
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

let on_sub_wp_eff_combinators #m {|d : lvm m |} (wpcs : wp_eff_combinators) : m wp_eff_combinators =
  let! ret_wp       = wpcs.ret_wp        |> f_tscheme in
  let! bind_wp      = wpcs.bind_wp       |> f_tscheme in
  let! stronger     = wpcs.stronger      |> f_tscheme in
  let! if_then_else = wpcs.if_then_else  |> f_tscheme in
  let! ite_wp       = wpcs.ite_wp        |> f_tscheme in
  let! close_wp     = wpcs.close_wp      |> f_tscheme in
  let! trivial      = wpcs.trivial       |> f_tscheme in

  let! repr        = wpcs.repr        |> map_optM (f_tscheme #m #d) in // FIXME: implicits
  let! return_repr = wpcs.return_repr |> map_optM (f_tscheme #m #d) in
  let! bind_repr   = wpcs.bind_repr   |> map_optM (f_tscheme #m #d) in
  return <| {
    ret_wp;
    bind_wp;
    stronger;
    if_then_else;
    ite_wp;
    close_wp;
    trivial;

    repr;
    return_repr;
    bind_repr;
  }

let mapTuple2 #m {| monad m |} (f : 'a -> m 'b) (g : 'c -> m 'd) (t : 'a & 'c) : m ('b & 'd) =
  Mktuple2 <$> f t._1 <*> g t._2

let mapTuple3 #m {| monad m |} (f : 'a -> m 'b) (g : 'c -> m 'd) (h : 'e -> m 'f) (t : 'a & 'c & 'e) : m ('b & 'd & 'f) =
  Mktuple3 <$> f t._1 <*> g t._2 <*> h t._3

let on_sub_layered_eff_combinators #m {|d : lvm m |} (lecs : layered_eff_combinators) : m layered_eff_combinators =
  let! l_repr         = lecs.l_repr         |> mapTuple2 (f_tscheme #m #d) (f_tscheme #m #d) in
  let! l_return       = lecs.l_return       |> mapTuple2 (f_tscheme #m #d) (f_tscheme #m #d) in
  let! l_bind         = lecs.l_bind         |> mapTuple3 (f_tscheme #m #d) (f_tscheme #m #d) return in
  let! l_subcomp      = lecs.l_subcomp      |> mapTuple3 (f_tscheme #m #d) (f_tscheme #m #d) return in
  let! l_if_then_else = lecs.l_if_then_else |> mapTuple3 (f_tscheme #m #d) (f_tscheme #m #d) return in
  let! l_close        = lecs.l_close        |> map_optM (mapTuple2 (f_tscheme #m #d) (f_tscheme #m #d)) in
  return <| {
    l_repr;
    l_return;
    l_bind;
    l_subcomp;
    l_if_then_else;
    l_close;
  }

let on_sub_combinators #m {|d : lvm m |} (cbs : eff_combinators) : m eff_combinators =
  match cbs with
  | Primitive_eff wpcs ->
    let! wpcs = on_sub_wp_eff_combinators wpcs in
    return <| Primitive_eff wpcs

  | DM4F_eff wpcs ->
    let! wpcs = on_sub_wp_eff_combinators wpcs in
    return <| DM4F_eff wpcs

  | Layered_eff lecs ->
    let! lecs = on_sub_layered_eff_combinators lecs in
    return <| Layered_eff lecs

let on_sub_effect_signature #m {|d : lvm m |} (es : effect_signature) : m effect_signature =
  match es with
  | Layered_eff_sig (n, (us, t)) ->
    let! t = f_term t in
    return <| Layered_eff_sig (n, (us, t))

  | WP_eff_sig (us, t) ->
    let! t = f_term t in
    return <| WP_eff_sig (us, t)

let on_sub_action #m {|d : lvm m |} (a : action) : m action =
  let  action_name             = a.action_name in
  let  action_unqualified_name = a.action_unqualified_name in
  let  action_univs            = a.action_univs in
  let! action_params           = a.action_params |> mapM f_binder in
  let! action_defn             = a.action_defn |> f_term in
  let! action_typ              = a.action_typ |> f_term in
  return <| {
    action_name;
    action_unqualified_name;
    action_univs;
    action_params;
    action_defn;
    action_typ;
  }

let rec on_sub_sigelt' #m {|d : lvm m |} (se : sigelt') : m sigelt' =
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
    let  univs           = ed.univs in
    let! binders         = ed.binders |> mapM f_binder in
    let! signature       = ed.signature |> on_sub_effect_signature in
    let! combinators     = ed.combinators |> on_sub_combinators in
    let! actions         = ed.actions |> mapM on_sub_action in
    let! eff_attrs       = ed.eff_attrs |> mapM f_term in
    let  extraction_mode = ed.extraction_mode in
    let ed = { mname; cattributes; univs; binders; signature; combinators; actions; eff_attrs; extraction_mode; } in
    return <| Sig_new_effect ed

  | Sig_sub_effect se ->
    let  source  = se.source in
    let  target  = se.target in
    let! lift_wp = se.lift_wp |> map_optM (f_tscheme #m #d) in
    let! lift    = se.lift    |> map_optM (f_tscheme #m #d) in
    let  kind    = se.kind in
    return <| Sig_sub_effect { source; target; lift_wp; lift; kind; }

  | Sig_effect_abbrev {lid; us; bs; comp; cflags} ->
    let! binders = bs |> mapM f_binder in
    let! comp    = comp |> f_comp in
    let! cflags  = cflags |> mapM (__on_decreases f_term) in
    // ^ review: residual flags should not have terms
    return <| Sig_effect_abbrev {lid; us; bs; comp; cflags}

  (* No content, except for Check. *)
  | Sig_pragma (Check t) ->
    let! t = f_term t in
    return <| Sig_pragma (Check t)
  | Sig_pragma _ -> return se

  | Sig_polymonadic_bind {m_lid; n_lid; p_lid; tm; typ; kind} ->
    let! tm  = f_tscheme tm in
    let! typ = f_tscheme typ in
    return <| Sig_polymonadic_bind {m_lid; n_lid; p_lid; tm; typ; kind}

  | Sig_polymonadic_subcomp {m_lid;
                             n_lid;
                             tm;
                             typ;
                             kind} ->
    let! tm  = f_tscheme tm in
    let! typ = f_tscheme typ in
    return <| Sig_polymonadic_subcomp {m_lid; n_lid; tm; typ; kind}

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

and on_sub_sigelt #m {|d : lvm m |} (se : sigelt) : m sigelt =
  let! sigel    = se.sigel |> on_sub_sigelt' in
  let  sigrng   = se.sigrng in
  let  sigquals = se.sigquals in
  let  sigmeta  = se.sigmeta in
  let! sigattrs = se.sigattrs |> mapM f_term in
  let  sigopts  = se.sigopts in
  let  sigopens_and_abbrevs = se.sigopens_and_abbrevs in
  return <| { sigel; sigrng; sigquals; sigmeta; sigattrs; sigopts; sigopens_and_abbrevs; }

let (>>=) (#m:_) {|monad m|} #a #b (c : m a) (f : a -> m b) =
  let! x = c in f x

let (<<|) (#m:_) {|monad m|} #a #b (f : a -> m b) (c : m a) : m b=
  let! x = c in f x

// Bottom up. The record is a reference so it can be easily cyclic.
let tie_bu (#m : Type -> Type) {| md : monad m |} (d : lvm m) : lvm m =
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

let visitM_term_univs #m {| md : monad m |} (proc_quotes : bool) vt vu (tm : term) : m term =
  let dict : lvm m =
    tie_bu #m #md { novfs #m #md with f_term = vt; f_univ = vu; proc_quotes = proc_quotes }
  in
  f_term #_ #dict tm

let visitM_term #m {| md : monad m |} (proc_quotes : bool) vt (tm : term) : m term =
  visitM_term_univs true vt return tm

let visitM_sigelt #m {| md : monad m |} (proc_quotes : bool) vt vu (tm : sigelt) : m sigelt =
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
