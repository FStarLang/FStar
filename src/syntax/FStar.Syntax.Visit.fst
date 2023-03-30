module FStar.Syntax.Visit

open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Compiler.Util

open FStar.Syntax
open FStar.Syntax.Syntax

type endo a = a -> a
let id #a (x:a) : a = x

type vfs_t = {
  f_term          : endo term;
  f_binder        : endo binder;
  f_binding_bv    : endo bv;
  f_br            : endo branch;
  f_comp          : endo comp;
  f_residual_comp : endo residual_comp;
  f_univ          : endo universe;
}

let on_tuple2 f g   (x, y)    = (f x, g y)
let on_tuple3 f g h (x, y, z) = (f x, g y, h z)

let novfs = {
  f_term          = id;
  f_binder        = id;
  f_binding_bv    = id;
  f_br            = id;
  f_comp          = id;
  f_residual_comp = id;
  f_univ          = id;
}

(* The two points of interest *)
let f_term           vfs = vfs.f_term
let f_univ           vfs = vfs.f_univ

let on_sub_arg vfs (a : arg) : arg =
  let (t, q) = a in
  let t = (f_term vfs) t in
  let q = map_opt q (function {aqual_implicit=i; aqual_attributes=attrs} ->
                      {aqual_implicit=i; aqual_attributes = map (f_term vfs) attrs}) in
  (t, q)

let on_sub_tscheme vfs (ts : tscheme) : tscheme =
  let (us, t) = ts in
  let t = f_term vfs t in
  (us, t)

(* Homeomorphic calls... for now *)
let f_arg            vfs = on_sub_arg vfs
let f_binding_bv     vfs = vfs.f_binding_bv
let f_binder         vfs = vfs.f_binder
let f_br             vfs = vfs.f_br
let f_comp           vfs = vfs.f_comp
let f_residual_comp  vfs = vfs.f_residual_comp
let f_tscheme        vfs = on_sub_tscheme vfs

let on_sub_meta vfs (md : metadata) : metadata =
  match md with
  | Meta_pattern (pats, args) ->
    let pats = map (f_term vfs) pats in
    let args = map (map (f_arg vfs)) args in
    Meta_pattern (pats, args)

  | Meta_monadic (m, typ) ->
    Meta_monadic (m, (f_term vfs) typ)

  | Meta_monadic_lift (m1, m2, typ) ->
    Meta_monadic_lift (m1, m2, (f_term vfs) typ)

  (* no subterms *)
  | md -> md

let on_sub_letbinding vfs (lb : letbinding) : letbinding =
  {
    lbname  = (match lb.lbname with
               | Inl bv -> Inl ((f_binding_bv vfs) bv)
               | Inr fv -> Inr fv);
    lbunivs = lb.lbunivs;
    lbtyp   = (f_term vfs) lb.lbtyp;
    lbeff   = lb.lbeff;
    lbattrs = map (f_term vfs) lb.lbattrs;
    lbpos   = lb.lbpos;
    lbdef   = (f_term vfs) lb.lbdef;
  }

let on_sub_ascription vfs (a : ascription) : ascription =
  let (tc, tacopt, b) = a in
  let tc = match tc with
           | Inl t -> Inl ((f_term vfs) t)
           | Inr c -> Inr ((f_comp vfs) c)
  in
  let tacopt = map_opt tacopt (f_term vfs) in
  (tc, tacopt, b)

(* Compress+unlazy *)
let rec compress (tm:term) : term =
  let tm = Subst.compress tm in
  match tm.n with
  (* unfold and retry *)
  | Tm_lazy li ->
    let tm' = must !lazy_chooser li.lkind li in
    compress tm'

  | _ -> tm

(* Not recursive itself! his does not apply anything deeply! The
recursion on deep subterms comes from the knot being tied below. *)
let on_sub_term vfs (tm : term) : term =
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
    tm

  | Tm_uinst (f, us) ->
    let us = map (f_univ vfs) us in
    mk (Tm_uinst (f, us))

  | Tm_type u ->
    mk (Tm_type ((f_univ vfs) u))

  | Tm_app (hd, args) ->
    let hd    = (f_term vfs) hd in
    let args  = map (f_arg vfs) args in
    mk (Tm_app (hd, args))

  | Tm_abs (bs, t, rc_opt) ->
    let bs     = map (f_binder vfs) bs in
    let t      = (f_term vfs) t in
    let rc_opt = map_opt rc_opt (f_residual_comp vfs) in
    mk (Tm_abs (bs, t, rc_opt))

  | Tm_arrow (bs, c) ->
    let bs    = map (f_binder vfs) bs in
    let c     = (f_comp vfs) c in
    mk (Tm_arrow (bs, c))

  | Tm_refine (bv, phi) ->
    let bv    = (f_binding_bv vfs) bv in
    let phi   = (f_term vfs) phi in
    mk (Tm_refine (bv, phi))

  | Tm_match (sc, asc_opt, brs, rc_opt) ->
    let sc      = (f_term vfs) sc in
    let asc_opt = map_opt asc_opt (fun (b, asc) -> ((f_binder vfs) b, on_sub_ascription vfs asc)) in
    let brs     = map (f_br vfs) brs in
    let rc_opt = map_opt rc_opt (f_residual_comp vfs) in
    mk (Tm_match (sc, asc_opt, brs, rc_opt))

  | Tm_ascribed (e, a, lopt) ->
    let e = (f_term vfs) e in
    let a = on_sub_ascription vfs a in
    mk (Tm_ascribed (e, a, lopt))

  | Tm_let ((is_rec, lbs), t) ->
    let lbs = map (on_sub_letbinding vfs) lbs in
    let t = (f_term vfs) t in
    mk (Tm_let ((is_rec, lbs), t))

  | Tm_quoted (tm, qi) ->
    let tm = (f_term vfs) tm in
    let qi = Syntax.on_antiquoted (f_term vfs) qi in
    mk (Tm_quoted (tm, qi))

  | Tm_meta (t, md) ->
    let t   = (f_term vfs) t in
    let md  = on_sub_meta vfs md in
    mk (Tm_meta (t, md))

let on_sub_binding_bv vfs (x : bv) : bv =
  { x with sort = (f_term vfs) x.sort }

let on_sub_binder vfs (b : binder) : binder =
  {
    binder_bv = (f_binding_bv vfs) b.binder_bv;
    binder_qual = map_opt b.binder_qual
                    (function Meta t -> Meta ((f_term vfs) t)
                            | q -> q);
    binder_attrs = map (f_term vfs) b.binder_attrs;
  }

let rec on_sub_pat vfs (p0 : pat) : pat =
  let mk p = { v=p; p=p0.p } in
  match p0.v with
  | Pat_constant _ ->
    p0

  | Pat_cons (fv, us, subpats) ->
    let us = map_opt us (map (f_univ vfs)) in
    let subpats = map (fun (p, b) -> (on_sub_pat vfs p, b)) subpats in
    mk (Pat_cons (fv, us, subpats))

  | Pat_var bv ->
    mk (Pat_var ((f_binding_bv vfs) bv))

  | Pat_wild bv ->
    mk (Pat_wild ((f_binding_bv vfs) bv))

  | Pat_dot_term t ->
    mk (Pat_dot_term (map_opt t (f_term vfs)))

let on_sub_br vfs br =
  let (pat, wopt, body) = br in
  (on_sub_pat vfs pat,
   map_opt wopt (f_term vfs),
   (f_term vfs) body)

let on_sub_comp_typ vfs ct =
  {
    comp_univs  = map (f_univ vfs) ct.comp_univs;
    effect_name = ct.effect_name;
    result_typ  = (f_term vfs) ct.result_typ;
    effect_args = ct.effect_args;
    flags       = ct.flags;
  }

let on_sub_comp vfs c =
  let cn =
    match c.n with
    | Total typ  -> Total ((f_term vfs) typ)
    | GTotal typ -> GTotal ((f_term vfs) typ)
    | Comp ct -> Comp (on_sub_comp_typ vfs ct)
  in
  Syntax.mk cn c.pos

let __on_decreases f : cflag -> cflag = function
  | DECREASES (Decreases_lex l)      -> DECREASES (Decreases_lex (map f l))
  | DECREASES (Decreases_wf  (r, t)) -> DECREASES (Decreases_wf (f r, f t))
  | f -> f

let on_sub_residual_comp vfs (rc : residual_comp) : residual_comp =
  {
    residual_effect = rc.residual_effect;
    residual_typ    = map_opt rc.residual_typ (f_term vfs);
    residual_flags  = map (__on_decreases (f_term vfs)) rc.residual_flags;
    // ^ review: residual flags should not have terms
  }

let on_sub_univ vfs (u : universe) : universe =
  let u = Subst.compress_univ u in
  match u with
  | U_max us -> U_max (map (f_univ vfs) us)
  | U_succ u -> U_succ (f_univ vfs u)

  | U_zero
  | U_bvar _
  | U_name _
  | U_unknown
  | U_unif _ ->
    u

let on_sub_wp_eff_combinators vfs (wpcs : wp_eff_combinators) : wp_eff_combinators =
  {
    ret_wp       = f_tscheme vfs wpcs.ret_wp;
    bind_wp      = f_tscheme vfs wpcs.bind_wp;
    stronger     = f_tscheme vfs wpcs.stronger;
    if_then_else = f_tscheme vfs wpcs.if_then_else;
    ite_wp       = f_tscheme vfs wpcs.ite_wp;
    close_wp     = f_tscheme vfs wpcs.close_wp;
    trivial      = f_tscheme vfs wpcs.trivial;

    repr         = map_opt wpcs.repr (f_tscheme vfs);
    return_repr  = map_opt wpcs.return_repr (f_tscheme vfs);
    bind_repr    = map_opt wpcs.bind_repr (f_tscheme vfs);
  }

let on_sub_layered_eff_combinators vfs (lecs : layered_eff_combinators) : layered_eff_combinators =
  let f_tscheme = f_tscheme vfs in
  {
    l_repr         = on_tuple2 f_tscheme f_tscheme    lecs.l_repr;
    l_return       = on_tuple2 f_tscheme f_tscheme    lecs.l_return;
    l_bind         = on_tuple3 f_tscheme f_tscheme id lecs.l_bind;
    l_subcomp      = on_tuple3 f_tscheme f_tscheme id lecs.l_subcomp;
    l_if_then_else = on_tuple3 f_tscheme f_tscheme id lecs.l_if_then_else;
  }

let on_sub_combinators vfs (cbs : eff_combinators) : eff_combinators =
  match cbs with
  | Primitive_eff wpcs ->
    let wpcs = on_sub_wp_eff_combinators vfs wpcs in
    Primitive_eff wpcs

  | DM4F_eff wpcs ->
    let wpcs = on_sub_wp_eff_combinators vfs wpcs in
    DM4F_eff wpcs

  | Layered_eff lecs ->
    let lecs = on_sub_layered_eff_combinators vfs lecs in
    Layered_eff lecs

let on_sub_effect_signature vfs (es : effect_signature) : effect_signature =
  match es with
  | Layered_eff_sig (n, (us, t)) ->
    let t = f_term vfs t in
    Layered_eff_sig (n, (us, t))

  | WP_eff_sig (us, t) ->
    let t = f_term vfs t in
    WP_eff_sig (us, t)

let on_sub_action vfs (a : action) : action =
  {
    action_name             = a.action_name;
    action_unqualified_name = a.action_unqualified_name;
    action_univs            = a.action_univs;
    action_params           = map (f_binder vfs) a.action_params;
    action_defn             = f_term vfs a.action_defn;
    action_typ              = f_term vfs a.action_typ;
  }

let rec on_sub_sigelt' vfs (se : sigelt') : sigelt' =
  match se with
  | Sig_inductive_typ (lid, unames, bs, num_uniform, typ, mutuals, ctors) ->
    Sig_inductive_typ (lid, unames, map (f_binder vfs) bs, num_uniform, (f_term vfs) typ, mutuals, ctors)

  | Sig_bundle (ses, lids) ->
    Sig_bundle (map (on_sub_sigelt vfs) ses, lids)

  | Sig_datacon (dlid, unames, typ, tlid, nparams, mutuals) ->
    Sig_datacon (dlid, unames, (f_term vfs) typ, tlid, nparams, mutuals)

  | Sig_declare_typ (lid, unames, typ) ->
    Sig_declare_typ (lid, unames, (f_term vfs) typ)

  | Sig_let ((is_rec, lbs), mutuals) ->
    Sig_let ((is_rec, map (on_sub_letbinding vfs) lbs), mutuals)

  | Sig_assume (lid, unames, phi) ->
    Sig_assume (lid, unames, (f_term vfs) phi)

  | Sig_new_effect ed ->
    let ed = {
      mname       = ed.mname;
      cattributes = ed.cattributes;
      univs       = ed.univs;
      binders     = map (f_binder vfs) ed.binders;
      signature   = on_sub_effect_signature vfs ed.signature;
      combinators = on_sub_combinators vfs ed.combinators;
      actions     = map (on_sub_action vfs) ed.actions;
      eff_attrs   = map (f_term vfs) ed.eff_attrs;
      extraction_mode = ed.extraction_mode;
    }
    in
    Sig_new_effect ed

  | Sig_sub_effect se ->
    let se = {
      source  = se.source;
      target  = se.target;
      lift_wp = map_opt se.lift_wp (f_tscheme vfs);
      lift    = map_opt se.lift    (f_tscheme vfs);
      kind    = se.kind;
    }
    in
    Sig_sub_effect se

  | Sig_effect_abbrev (lid, univ_names, binders, comp, flags) ->
    let binders = map (f_binder vfs) binders in
    let comp    = f_comp vfs comp in
    let flags   = map (__on_decreases (f_term vfs)) flags in
    // ^ review: residual flags should not have terms
    Sig_effect_abbrev (lid, univ_names, binders, comp, flags)

  (* No content *)
  | Sig_pragma _ -> se

  | Sig_polymonadic_bind (m, n, p, (us_t, t), (us_ty, ty), k) ->
    let t  = f_term vfs t in
    let ty = f_term vfs ty in
    Sig_polymonadic_bind (m, n, p, (us_t, t), (us_ty, ty), k)

  | Sig_polymonadic_subcomp (m, n, (us_t, t), (us_ty, ty), k) ->
    let t  = f_term vfs t in
    let ty = f_term vfs ty in
    Sig_polymonadic_subcomp (m, n, (us_t, t), (us_ty, ty), k)

  | Sig_fail _
  | Sig_splice _ ->
    failwith "Sig_fail and Sig_splice not supported in visit"

  | _ -> failwith "sorry"

and on_sub_sigelt vfs (se : sigelt) : sigelt =
  {
    sigel    = on_sub_sigelt' vfs se.sigel;
    sigrng   = se.sigrng;
    sigquals = se.sigquals;
    sigmeta  = se.sigmeta;
    sigattrs = map (f_term vfs) se.sigattrs;
    sigopts  = se.sigopts;
  }

// Bottom up. The record is a reference so it can be easily cyclic.
let tie_bu (vfs:vfs_t) : ref vfs_t =
  // needs explicit eta to not loop?
  let r : ref vfs_t = mk_ref novfs in
  r :=
    {
      f_term          = (fun x -> f_term          vfs (on_sub_term          !r x));
      f_binding_bv    = (fun x -> f_binding_bv    vfs (on_sub_binding_bv    !r x));
      f_binder        = (fun x -> f_binder        vfs (on_sub_binder        !r x));
      f_br            = (fun x -> f_br            vfs (on_sub_br            !r x));
      f_comp          = (fun x -> f_comp          vfs (on_sub_comp          !r x));
      f_residual_comp = (fun x -> f_residual_comp vfs (on_sub_residual_comp !r x));
      f_univ          = (fun x -> f_univ          vfs (on_sub_univ          !r x));
    };
  r

let visit_term f (tm : term) : term =
  let r = !(tie_bu { novfs with f_term = f }) in
  r.f_term tm

let visit_term_univs f g (tm : term) : term =
  let r = !(tie_bu { novfs with f_term = f; f_univ = g }) in
  r.f_term tm

let visit_sigelt f g (se : sigelt) : sigelt =
  let r = !(tie_bu { novfs with f_term = f; f_univ = g }) in
  on_sub_sigelt r se
