module FStarC.Syntax.Visit

open FStarC
open FStarC.Syntax.Syntax
open FStarC.Effect
open FStarC.List

(* A direct implementation, not [VisitM] at the identity monad.  Going through
   [VisitM] meant a dictionary of visitors tied through a [ref], which every
   node of the term was dispatched through, and which no backend could
   specialize.  Here [vt] and [vu] are [monomorphize] binders, so Custard
   compiles a copy of the traversal per visitor, calling it directly.

   The traversal visits subterms in the same order as [VisitM] does: the order
   in which they are written below.  Several callers collect into a [ref], so
   this is observable. *)

module A = FStar.Attributes
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst

(* Compress+unlazy *)
let rec compress (tm:term) : ML term =
  let tm = SS.compress tm in
  match tm.n with
  | Tm_lazy li ->
    let tm' = Option.must !lazy_chooser li.lkind li in
    compress tm'
  | _ -> tm

let map_opt (#a #b:Type) ([@@@A.monomorphize] f : a -> ML b) (o : option a) : ML (option b) =
  match o with
  | None -> None
  | Some x -> Some (f x)

let rec f_term (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
               ([@@@A.monomorphize] vu : universe -> ML universe) (tm:term) : ML term =
  vt (on_sub_term pq vt vu tm)

and f_univ (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
           ([@@@A.monomorphize] vu : universe -> ML universe) (u:universe) : ML universe =
  let u = SS.compress_univ u in
  let u =
    match u with
    | U_max us -> U_max (map (f_univ pq vt vu) us)
    | U_succ u -> U_succ (f_univ pq vt vu u)
    | U_zero
    | U_bvar _
    | U_name _
    | U_unknown
    | U_unif _ -> u
  in
  vu u

and f_terms (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
            ([@@@A.monomorphize] vu : universe -> ML universe) (ts:list term) : ML (list term) =
  map (f_term pq vt vu) ts

and f_aqual (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
            ([@@@A.monomorphize] vu : universe -> ML universe) (aq:arg_qualifier) : ML arg_qualifier =
  let {aqual_implicit=i; aqual_attributes=attrs} = aq in
  let attrs = f_terms pq vt vu attrs in
  {aqual_implicit=i; aqual_attributes=attrs}

and f_arg (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
          ([@@@A.monomorphize] vu : universe -> ML universe) (a:arg) : ML arg =
  let (t, q) = a in
  let t = f_term pq vt vu t in
  let q = map_opt (f_aqual pq vt vu) q in
  (t, q)

and f_args (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
           ([@@@A.monomorphize] vu : universe -> ML universe) (args:list arg) : ML (list arg) =
  map (f_arg pq vt vu) args

and f_tscheme (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
              ([@@@A.monomorphize] vu : universe -> ML universe) (ts:tscheme) : ML tscheme =
  let (us, t) = ts in
  (us, f_term pq vt vu t)

and f_meta (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
           ([@@@A.monomorphize] vu : universe -> ML universe) (md:metadata) : ML metadata =
  match md with
  | Meta_pattern (pats, args) ->
    let pats = f_terms pq vt vu pats in
    let args = map (f_args pq vt vu) args in
    Meta_pattern (pats, args)
  | Meta_monadic (m, typ) -> Meta_monadic (m, f_term pq vt vu typ)
  | Meta_monadic_lift (m1, m2, typ) -> Meta_monadic_lift (m1, m2, f_term pq vt vu typ)
  | Meta_named _
  | Meta_labeled _
  | Meta_desugared _ -> md

and f_letbinding (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
                 ([@@@A.monomorphize] vu : universe -> ML universe) (lb:letbinding) : ML letbinding =
  let lbname =
    match lb.lbname with
    | Inl bv -> Inl (f_binding_bv pq vt vu bv)
    | Inr fv -> Inr fv
  in
  let lbunivs = lb.lbunivs in
  let lbtyp = f_term pq vt vu lb.lbtyp in
  let lbeff = lb.lbeff in
  let lbattrs = f_terms pq vt vu lb.lbattrs in
  let lbpos = lb.lbpos in
  let lbdef = f_term pq vt vu lb.lbdef in
  { lbname; lbunivs; lbtyp; lbeff; lbattrs; lbpos; lbdef; }

and f_ascription (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
                 ([@@@A.monomorphize] vu : universe -> ML universe) (a:ascription) : ML ascription =
  let (tc, tacopt, b) = a in
  let tc = match tc with
           | Inl t -> Inl (f_term pq vt vu t)
           | Inr c -> Inr (f_comp pq vt vu c)
  in
  let tacopt = map_opt (f_term pq vt vu) tacopt in
  (tc, tacopt, b)

(* Not recursive itself, beyond the immediate subterms. *)
and on_sub_term (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
                ([@@@A.monomorphize] vu : universe -> ML universe) (tm:term) : ML term =
  let mk t = S.mk t tm.pos in
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
    let f = f_term pq vt vu f in
    let us = map (f_univ pq vt vu) us in
    mk (Tm_uinst (f, us))

  | Tm_type u ->
    mk (Tm_type (f_univ pq vt vu u))

  | Tm_app {hd; arg} ->
    let hd = f_term pq vt vu hd in
    let arg = f_arg pq vt vu arg in
    mk (Tm_app {hd; arg})

  | Tm_abs {b; body=t; rc_opt} ->
    let b = f_binder pq vt vu b in
    let t = f_term pq vt vu t in
    let rc_opt = map_opt (f_residual_comp pq vt vu) rc_opt in
    mk (Tm_abs {b; body=t; rc_opt})

  | Tm_arrow {b; comp=c} ->
    let b = f_binder pq vt vu b in
    let c = f_comp pq vt vu c in
    mk (Tm_arrow {b; comp=c})

  | Tm_refine {b=bv; phi} ->
    let bv = f_binding_bv pq vt vu bv in
    let phi = f_term pq vt vu phi in
    mk (Tm_refine {b=bv; phi})

  | Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt} ->
    let sc = f_term pq vt vu sc in
    let asc_opt = map_opt (fun (b, asc) ->
                    let b = f_binder pq vt vu b in
                    let asc = f_ascription pq vt vu asc in
                    (b, asc)) asc_opt in
    let brs = map (f_br pq vt vu) brs in
    let rc_opt = map_opt (f_residual_comp pq vt vu) rc_opt in
    mk (Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt})

  | Tm_ascribed {tm=e; asc=a; eff_opt=lopt} ->
    let e = f_term pq vt vu e in
    let a = f_ascription pq vt vu a in
    mk (Tm_ascribed {tm=e; asc=a; eff_opt=lopt})

  | Tm_let {lbs=(is_rec, lbs); body=t} ->
    let lbs = map (f_letbinding pq vt vu) lbs in
    let t = f_term pq vt vu t in
    mk (Tm_let {lbs=(is_rec, lbs); body=t})

  | Tm_quoted (qtm, qi) ->
    if pq || qi.qkind = Quote_dynamic then
      mk (Tm_quoted (f_term pq vt vu qtm, qi))
    else
      tm

  | Tm_meta {tm=t; meta=md} ->
    let t = f_term pq vt vu t in
    let md = f_meta pq vt vu md in
    mk (Tm_meta {tm=t; meta=md})

and f_binding_bv (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
                 ([@@@A.monomorphize] vu : universe -> ML universe) (x:bv) : ML bv =
  { x with sort = f_term pq vt vu x.sort }

and f_binder (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
             ([@@@A.monomorphize] vu : universe -> ML universe) (b:binder) : ML binder =
  let binder_bv = f_binding_bv pq vt vu b.binder_bv in
  let binder_qual =
    match b.binder_qual with
    | Some (Meta t) -> Some (Meta (f_term pq vt vu t))
    | q -> q in
  let binder_positivity = b.binder_positivity in
  let binder_attrs = f_terms pq vt vu b.binder_attrs in
  { binder_bv; binder_qual; binder_positivity; binder_attrs; }

and f_pat (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
          ([@@@A.monomorphize] vu : universe -> ML universe) (p0:pat) : ML pat =
  let mk p = { v=p; p=p0.p } in
  match p0.v with
  | Pat_constant _ -> p0
  | Pat_cons (fv, us, subpats) ->
    let us = map_opt (map (f_univ pq vt vu)) us in
    let subpats = map (fun (p, b) -> (f_pat pq vt vu p, b)) subpats in
    mk (Pat_cons (fv, us, subpats))
  | Pat_var bv ->
    mk (Pat_var (f_binding_bv pq vt vu bv))
  | Pat_dot_term t ->
    mk (Pat_dot_term (map_opt (f_term pq vt vu) t))

and f_br (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
         ([@@@A.monomorphize] vu : universe -> ML universe) (br:branch) : ML branch =
  let (pat, wopt, body) = br in
  let pat = f_pat pq vt vu pat in
  let wopt = map_opt (f_term pq vt vu) wopt in
  let body = f_term pq vt vu body in
  (pat, wopt, body)

and f_cflag (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
            ([@@@A.monomorphize] vu : universe -> ML universe) (cf:cflag) : ML cflag =
  match cf with
  | SMTPAT p -> SMTPAT (f_term pq vt vu p)
  | DECREASES (Decreases_lex l) -> DECREASES (Decreases_lex (f_terms pq vt vu l))
  | DECREASES (Decreases_wf (r, t)) ->
    let r = f_term pq vt vu r in
    let t = f_term pq vt vu t in
    DECREASES (Decreases_wf (r, t))
  | f -> f

and f_comp (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
           ([@@@A.monomorphize] vu : universe -> ML universe) (c:comp) : ML comp =
  match c.n with
  | Comp ct ->
    let effect_name = ct.effect_name in
    let source_effect_name = ct.source_effect_name in
    let result_typ = f_term pq vt vu ct.result_typ in
    let flags = map (f_cflag pq vt vu) ct.flags in
    S.mk_comp' (Comp { effect_name; result_typ; flags; source_effect_name; }) c.pos

and f_residual_comp (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
                    ([@@@A.monomorphize] vu : universe -> ML universe) (rc:residual_comp)
  : ML residual_comp =
  let residual_effect = rc.residual_effect in
  let residual_typ = map_opt (f_term pq vt vu) rc.residual_typ in
  let residual_flags = map (f_cflag pq vt vu) rc.residual_flags in
  { residual_effect; residual_typ; residual_flags; }

let rec f_sigelt' (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
                  ([@@@A.monomorphize] vu : universe -> ML universe) (se:sigelt') : ML sigelt' =
  match se with
  | Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params } ->
    let params = map (f_binder pq vt vu) params in
    let t = f_term pq vt vu t in
    Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params }

  | Sig_bundle {ses; lids} ->
    Sig_bundle {ses = map (f_sigelt pq vt vu) ses; lids}

  | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params; proj_disc_lids} ->
    let t = f_term pq vt vu t in
    Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params; proj_disc_lids }

  | Sig_declare_typ {lid; us; t} ->
    Sig_declare_typ {lid; us; t = f_term pq vt vu t}

  | Sig_let {lbs=(is_rec, lbs); lids} ->
    Sig_let {lbs=(is_rec, map (f_letbinding pq vt vu) lbs); lids}

  | Sig_assume {lid; us; phi} ->
    Sig_assume {lid; us; phi = f_term pq vt vu phi}

  | Sig_new_effect ed ->
    let mname = ed.mname in
    let cattributes = ed.cattributes in
    let combinators =
      match ed.combinators with
      | None -> None
      | Some c ->
        let repr = f_tscheme pq vt vu c.repr in
        let return_repr = f_tscheme pq vt vu c.return_repr in
        let bind_repr = f_tscheme pq vt vu c.bind_repr in
        let repr_universe = f_tscheme pq vt vu c.repr_universe in
        Some { repr; return_repr; bind_repr; repr_universe }
    in
    let eff_attrs = f_terms pq vt vu ed.eff_attrs in
    let extraction_mode = ed.extraction_mode in
    Sig_new_effect { mname; cattributes; combinators; eff_attrs; extraction_mode; }

  | Sig_sub_effect se ->
    Sig_sub_effect { se with lift = map_opt (f_tscheme pq vt vu) se.lift }

  (* An effect abbreviation is a pair of names: no subterms to visit. *)
  | Sig_effect_abbrev _ -> se

  (* No content, except for Check. *)
  | Sig_pragma (Check t) -> Sig_pragma (Check (f_term pq vt vu t))
  | Sig_pragma (Eval t) -> Sig_pragma (Eval (f_term pq vt vu t))
  | Sig_pragma _ -> se

  (* These two below are hardly used, since they disappear after
  typechecking, but are still useful so the desugarer can make use of
  deep_compress_se. *)
  | Sig_fail {rng; errs; fail_in_lax; ses} ->
    Sig_fail {rng; errs; fail_in_lax; ses = map (f_sigelt pq vt vu) ses}

  | Sig_splice {is_typed; lids; tac} ->
    Sig_splice {is_typed; lids; tac = f_term pq vt vu tac}

  | _ -> failwith "on_sub_sigelt: missing case"

and f_sigelt (pq:bool) ([@@@A.monomorphize] vt : term -> ML term)
             ([@@@A.monomorphize] vu : universe -> ML universe) (se:sigelt) : ML sigelt =
  let sigel = f_sigelt' pq vt vu se.sigel in
  let sigattrs = f_terms pq vt vu se.sigattrs in
  { se with sigel; sigattrs }

[@@A.custard_inline]
let visit_term pq ([@@@A.monomorphize] vt) t =
  f_term true vt (fun u -> u) t

[@@A.custard_inline]
let visit_term_univs pq ([@@@A.monomorphize] vt) ([@@@A.monomorphize] vu) t =
  f_term pq vt vu t

(* [proc_quotes] is ignored here, and quotes are always visited, as they
   always have been. *)
[@@A.custard_inline]
let visit_sigelt pq ([@@@A.monomorphize] vt) ([@@@A.monomorphize] vu) se =
  f_sigelt pq vt vu se
