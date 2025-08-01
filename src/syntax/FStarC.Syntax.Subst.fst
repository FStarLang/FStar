(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Syntax.Subst
open FStarC.Effect
open FStarC.List

open FStarC
open FStarC.Range
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Ident

module U = FStarC.Util
module S = FStarC.Syntax.Syntax

///////////////////////////////////////////////////////////////////////////
// A few utility functions for working with lists of parallel substitutions
///////////////////////////////////////////////////////////////////////////

(* A subst_t is a composition of parallel substitutions, expressed as a list of lists *)
let subst_to_string s =
    s |> List.map (fun (b, _) -> (string_of_id b.ppname)) |> String.concat ", "

(* apply_until_some f s
      applies f to each element of s until it returns (Some t)
*)
let rec apply_until_some f s =
    match s with
    | [] -> None
    | s0::rest ->
        match f s0 with
        | None -> apply_until_some f rest
        | Some st -> Some (rest, st)

let map_some_curry f x = function
    | None -> x
    | Some (a, b) -> f a b

let apply_until_some_then_map f s g t =
    apply_until_some f s
    |> map_some_curry g t
/////////////////////////////////////////////////////////////////////////


//s1 is the subsitution already associated with this node;
//s2 is the new subsitution to add to it
//compose substitutions by concatenating them
//the order of concatenation is important!
//the range of s2 take precedence, if present
let compose_subst s1 s2 =
    let s = fst s1 @ fst s2 in
    let ropt = match snd s2 with
               | SomeUseRange _ -> snd s2
               | _ -> snd s1 in
    (s, ropt)

//apply a delayed substitution s to t,
//composing it with any other delayed substitution that may already be there
let delay t s =
 match t.n with
 | Tm_delayed {tm=t'; substs=s'} ->
    //s' is the subsitution already associated with this node;
    //s is the new subsitution to add to it
    //compose substitutions by concatenating them
    //the order of concatenation is important!
    mk_Tm_delayed (t', compose_subst s' s) t.pos
 | _ ->
    mk_Tm_delayed (t, s) t.pos

(*
    force_uvar' (t:term) : term * bool
        replaces any unification variable at the head of t
        with the term that it has been fixed to, if any.

        Also returns `true`, if it actually resolved the uvar at the head
                     `false` otherwise

      Warning: if force_uvar changes to operate on inputs other
      than Tm_uvar then the fastpath out match in compress will
      need to be updated.
*)
let rec force_uvar' t =
  match t.n with
  | Tm_uvar ({ctx_uvar_head=uv}, s) ->
      (match Unionfind.find uv with
          | Some t' -> fst (force_uvar' (delay t' s)), true
          | _ -> t, false)
  | _ -> t, false

//wraps force_uvar' to propagate any position information
//from the uvar to anything it may have been resolved to
let force_uvar t =
  let t', forced = force_uvar' t in
  if forced
  then delay t' ([], SomeUseRange t.pos)
  else t

let rec compress_univ u = match u with
    | U_unif u' ->
      begin match Unionfind.univ_find u' with
        | Some u -> compress_univ u
        | _ -> u
      end
    | _ -> u

(********************************************************************************)
(*************************** Delayed substitutions ******************************)
(********************************************************************************)

//Lookup a bound var or a name in a parallel substitution
let subst_bv a s = U.find_map s (function
    | DB (i, x) when (i=a.index) ->
      Some (bv_to_name (Syntax.set_range_of_bv x (Syntax.range_of_bv a)))
    | DT (i, t) when (i=a.index) ->
      Some t
    | _ -> None)
let subst_nm a s = U.find_map s (function
    | NM (x, i) when bv_eq a x -> Some (bv_to_tm ({a with index=i}))
    | NT (x, t) when bv_eq a x -> Some t
    | _ -> None)
let subst_univ_bv x s = U.find_map s (function
    | UN(y, t) when (x=y) -> Some t
    | _ -> None)
let subst_univ_nm (x:univ_name) s = U.find_map s (function
    | UD(y, i) when (ident_equals x y) -> Some (U_bvar i)
    | _ -> None)

let rec subst_univ s u =
    let u = compress_univ u in
    match u with
      | U_bvar x ->
        apply_until_some_then_map (subst_univ_bv x) s subst_univ u

      | U_name  x ->
        apply_until_some_then_map (subst_univ_nm x) s subst_univ u

      | U_zero
      | U_unknown
      | U_unif _ -> u
      | U_succ u -> U_succ (subst_univ s u)
      | U_max us -> U_max (List.map (subst_univ s) us)

let tag_with_range t s =
    match snd s with
    | NoUseRange -> t
    | SomeUseRange r ->
      if Range.rng_included (Range.use_range t.pos) (Range.use_range r)
      then t
      else begin
      let r = Range.set_use_range t.pos (Range.use_range r) in
      let t' = match t.n with
        | Tm_bvar bv -> Tm_bvar (Syntax.set_range_of_bv bv r)
        | Tm_name bv -> Tm_name (Syntax.set_range_of_bv bv r)
        | Tm_fvar fv -> let l = Syntax.lid_of_fv fv in
                        let v = {fv.fv_name with v=Ident.set_lid_range l r} in
                        let fv = {fv with fv_name=v} in
                        Tm_fvar fv
        | t' -> t' in
      {t with n=t'; pos=r}
      end

let tag_lid_with_range l s =
    match (snd s) with
    | NoUseRange -> l
    | SomeUseRange r ->
      if Range.rng_included (Range.use_range (Ident.range_of_lid l)) (Range.use_range r)
      then l
      else Ident.set_lid_range l (Range.set_use_range (Ident.range_of_lid l) (Range.use_range r))

let mk_range r (s:subst_ts) =
    match snd s with
    | NoUseRange -> r
    | SomeUseRange r' ->
      if Range.rng_included (Range.use_range r) (Range.use_range r')
      then r
      else Range.set_use_range r (Range.use_range r')

(* Applies a substitution to a node,
     immediately if it is a variable
     or builds a delayed node otherwise *)
let rec subst' (s:subst_ts) (t:term) : term =
  let subst_tail (tl:list (list subst_elt)) = subst' (tl, snd s) in
  match s with
  | [], NoUseRange
  | [[]], NoUseRange -> t
  | _ ->
    let t0 = t in
    match t0.n with
    | Tm_unknown
    | Tm_constant _                      //a constant cannot be substituted
    | Tm_fvar _ -> tag_with_range t0 s   //fvars are never subject to substitution

    | Tm_delayed {tm=t';substs=s'} ->
        //s' is the subsitution already associated with this node;
        //s is the new subsitution to add to it
        //compose substitutions by concatenating them
        //the order of concatenation is important!
        mk_Tm_delayed (t', compose_subst s' s) t.pos

    | Tm_bvar a ->
        apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0

    | Tm_name a ->
        apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0

    | Tm_type u ->
        mk (Tm_type (subst_univ (fst s) u)) (mk_range t0.pos s)

    | _ ->
      //NS: 04/12/2018
      //    Substitutions on Tm_uvar just gets delayed
      //    since its solution may eventually end up being an open term
      mk_Tm_delayed (t0, s) (mk_range t.pos s)

let subst_dec_order' s = function
  | Decreases_lex l -> Decreases_lex (l |> List.map (subst' s))
  | Decreases_wf (rel, e) -> Decreases_wf (subst' s rel, subst' s e)

let subst_flags' s flags =
    flags |> List.map (function
        | DECREASES dec_order -> DECREASES (subst_dec_order' s dec_order)
        | f -> f)

let subst_bqual' s i =
  match i with
  | Some (Meta t) -> Some (Meta (subst' s t))
  | _ -> i

let subst_aqual' s (i:aqual) : aqual =
  match i with
  | None -> None
  | Some a -> Some ({a with aqual_attributes = List.map (subst' s) a.aqual_attributes })

let subst_comp_typ' s t =
  match s with
  | [], NoUseRange
  | [[]], NoUseRange -> t
  | _ ->
    {t with effect_name=tag_lid_with_range t.effect_name s;
            comp_univs=List.map (subst_univ (fst s)) t.comp_univs;
            result_typ=subst' s t.result_typ;
            flags=subst_flags' s t.flags;
            effect_args=List.map (fun (t, imp) -> subst' s t, subst_aqual' s imp) t.effect_args}

let subst_comp' s t =
  match s with
  | [], NoUseRange
  | [[]], NoUseRange -> t
  | _ ->
    match t.n with
      | Total t -> mk_Total (subst' s t)
      | GTotal t -> mk_GTotal (subst' s t)
      | Comp ct -> mk_Comp(subst_comp_typ' s ct)

let subst_ascription' s (asc:ascription) =
  let annot, topt, use_eq = asc in
  let annot = match annot with
              | Inl t -> Inl (subst' s t)
              | Inr c -> Inr (subst_comp' s c) in
  annot,
  Option.map (subst' s) topt,
  use_eq

let shift n s = match s with
    | DB(i, t) -> DB(i+n, t)
    | DT(i, t) -> DT(i+n, t)
    | UN(i, t) -> UN(i+n, t)
    | NM(x, i) -> NM(x, i+n)
    | UD(x, i) -> UD(x, i+n)
    | NT _  -> s
let shift_subst n s = List.map (shift n) s
let shift_subst' n s = fst s |> List.map (shift_subst n), snd s
let subst_binder' s b =
  S.mk_binder_with_attrs
    ({ b.binder_bv with sort = subst' s b.binder_bv.sort })
    (subst_bqual' s b.binder_qual)
    b.binder_positivity
    (b.binder_attrs |> List.map (subst' s))

let subst_binder s (b:binder) = subst_binder' ([s], NoUseRange) b

let subst_binders' s bs =
    bs |> List.mapi (fun i b ->
        if i=0 then subst_binder' s b
        else subst_binder' (shift_subst' i s) b)
let subst_binders s (bs:binders) = subst_binders' ([s], NoUseRange) bs


// NOTE: We don't descend into `imp` here since one cannot *apply* a
// `Meta t` argument, so this would always be a no-op
let subst_arg' s (t, imp) = (subst' s t, imp)

let subst_args' s = List.map (subst_arg' s)

let subst_univs_opt sub us_opt = 
    match us_opt with
    | None -> None
    | Some us -> Some (List.map (subst_univ sub) us)

let subst_pat' s p : (pat & int) =
    let rec aux n p : (pat & int) = match p.v with
      | Pat_constant _ -> p, n

      | Pat_cons(fv, us_opt, pats) ->
        let us_opt = subst_univs_opt (fst (shift_subst' n s)) us_opt in
        let pats, n = pats |> List.fold_left (fun (pats, n) (p, imp) ->
            let p, m = aux n p in
            ((p,imp)::pats, m)) ([], n) in
        {p with v=Pat_cons(fv, us_opt, List.rev pats)}, n

      | Pat_var x ->
        let s = shift_subst' n s in
        let x = {x with sort=subst' s x.sort} in
        {p with v=Pat_var x}, n + 1

      | Pat_dot_term eopt ->
        let s = shift_subst' n s in
        let eopt = Option.map (subst' s) eopt in
        {p with v=Pat_dot_term eopt}, n
  in aux 0 p

let push_subst_lcomp s lopt = match lopt with
    | None -> None
    | Some rc ->
        let residual_typ = Option.map (subst' s) rc.residual_typ in
        (* NB: residual flags MUST be closed. DECREASES cannot
        appear there *)
        let rc = { residual_effect = rc.residual_effect
                 ; residual_typ    = residual_typ
                 ; residual_flags  = rc.residual_flags } in
        Some rc

let compose_uvar_subst (u:ctx_uvar) (s0:subst_ts) (s:subst_ts) : subst_ts =
    let should_retain x =
        u.ctx_uvar_binders |> U.for_some (fun b -> S.bv_eq x b.binder_bv)
    in
    let rec aux = function
        | [] -> []
        | hd_subst::rest ->
          let hd =
              hd_subst |> List.collect (function
              | NT(x, t) ->
                if should_retain x
                then [NT(x, delay t (rest, NoUseRange))]
                else []
              | NM(x, i) ->
                if should_retain x
                then let x_i = S.bv_to_tm ({x with index=i}) in
                     let t = subst' (rest, NoUseRange) x_i in
                     match t.n with
                     | Tm_bvar x_j -> [NM(x, x_j.index)]
                     | _ -> [NT(x, t)]
                else []
              | _ -> [])
          in
          hd @ aux rest
    in
    match aux (fst s0 @ fst s) with
    | [] -> [], snd s
    |  s' -> [s'], snd s

//
// If resolve_uvars is true, it will lookup the unionfind graph
//   and use uvar solution, if it has already been solved
//   see the Tm_uvar case in this function
// Otherwise it will just compose s with the uvar subst
// 
let rec push_subst_aux (resolve_uvars:bool) s t =
    //makes a syntax node, setting it's use range as appropriate from s
    let mk t' = Syntax.mk t' (mk_range t.pos s) in
    match t.n with
    | Tm_delayed _ -> failwith "Impossible (delayed node in push_subst)"

    | Tm_lazy i ->
        begin match i.lkind with
        | Lazy_embedding _ ->
            (* These might be open! Just unfold and descend.
             * The hope is that this does not occur often and so
             * we still get good performance. *)
          let t = Option.must !lazy_chooser i.lkind i in // Can't call Syntax.Util from here
          push_subst_aux resolve_uvars s t
        | _ ->
            (* All others must be closed, so don't bother *)
            tag_with_range t s
        end

    | Tm_constant _
    | Tm_fvar _
    | Tm_unknown -> tag_with_range t s //these are always closed

    | Tm_uvar (uv, s0) ->
      let fallback () =
        tag_with_range ({t with n = Tm_uvar(uv, compose_uvar_subst uv s0 s)}) s
      in
      if not resolve_uvars
      then fallback ()
      else (match (Unionfind.find uv.ctx_uvar_head) with
            | None -> fallback ()
            | Some t -> push_subst_aux resolve_uvars (compose_subst s0 s) t)

    | Tm_type _
    | Tm_bvar _
    | Tm_name _  -> subst' s t

    | Tm_uinst(t', us) ->
        //t' must be an fvar---it cannot be substituted
        //but the universes may be substituted
        let us = List.map (subst_univ (fst s)) us in
        tag_with_range (mk (Tm_uinst (t', us))) s

    | Tm_app {hd=t0; args} -> mk (Tm_app {hd=subst' s t0; args=subst_args' s args})

    | Tm_ascribed {tm=t0; asc; eff_opt=lopt} ->
      mk (Tm_ascribed {tm=subst' s t0; asc=subst_ascription' s asc; eff_opt=lopt})

    | Tm_abs {bs; body; rc_opt=lopt} ->
        let n = List.length bs in
        let s' = shift_subst' n s in
        mk (Tm_abs {bs=subst_binders' s bs; body=subst' s' body; rc_opt=push_subst_lcomp s' lopt})

    | Tm_arrow {bs; comp} ->
        let n = List.length bs in
        mk (Tm_arrow {bs=subst_binders' s bs;comp=subst_comp' (shift_subst' n s) comp})

    | Tm_refine {b=x; phi} ->
        let x = {x with sort=subst' s x.sort} in
        let phi = subst' (shift_subst' 1 s) phi in
        mk (Tm_refine {b=x; phi})

    | Tm_match {scrutinee=t0; ret_opt=asc_opt; brs=pats; rc_opt=lopt} ->
        let t0 = subst' s t0 in
        let pats = pats |> List.map (fun (pat, wopt, branch) ->
          let pat, n = subst_pat' s pat in
          let s = shift_subst' n s in
          let wopt = match wopt with
            | None -> None
            | Some w -> Some (subst' s w) in
          let branch = subst' s branch in
          (pat, wopt, branch)) in
        let asc_opt =
          match asc_opt with
          | None -> None
          | Some (b, asc) ->
            let b = subst_binder' s b in
            let asc = subst_ascription' (shift_subst' 1 s) asc in
            Some (b, asc) in
        mk (Tm_match {scrutinee=t0; ret_opt=asc_opt; brs=pats; rc_opt=push_subst_lcomp s lopt})

    | Tm_let {lbs=(is_rec, lbs); body} ->
        let n = List.length lbs in
        let sn = shift_subst' n s in
        let body = subst' sn body in
        let lbs = lbs |> List.map (fun lb ->
          let lbt = subst' s lb.lbtyp in
          let lbd = if is_rec && Inl? (lb.lbname) //if it is a recursive local let, then all the let bound names are in scope for the body
                    then subst' sn lb.lbdef
                    else subst' s lb.lbdef in
          let lbname = match lb.lbname with
              | Inl x -> Inl ({x with sort=lbt})
              | Inr fv -> Inr fv
          in
          let lbattrs = List.map (subst' s) lb.lbattrs in
          {lb with lbname=lbname; lbtyp=lbt; lbdef=lbd; lbattrs=lbattrs}) in
        mk (Tm_let {lbs=(is_rec, lbs); body})

    | Tm_meta {tm=t0; meta=Meta_pattern (bs, ps)} ->
        mk (Tm_meta {tm=subst' s t0; meta=Meta_pattern (List.map (subst' s) bs, ps |> List.map (subst_args' s))})

    | Tm_meta {tm=t0; meta=Meta_monadic (m, t)} ->
        mk (Tm_meta {tm=subst' s t0; meta=Meta_monadic(m, subst' s t)})

    | Tm_meta {tm=t0; meta=Meta_monadic_lift (m1, m2, t)} ->
        mk (Tm_meta {tm=subst' s t0; meta=Meta_monadic_lift (m1, m2, subst' s t)})

    | Tm_quoted (tm, qi) ->
        begin match qi.qkind with
        | Quote_dynamic -> mk (Tm_quoted (subst' s tm, qi))
        | Quote_static ->
            let qi = on_antiquoted (subst' s) qi in
            mk (Tm_quoted (tm, qi))
        end

    | Tm_meta {tm=t; meta=m} ->
        mk (Tm_meta {tm=subst' s t; meta=m})

let push_subst s t = push_subst_aux true s t

//
// Only push the pending substitution down,
//   no resolving uvars
//
let compress_subst t =
  match t.n with
  | Tm_delayed {tm=t; substs=s} ->
    let resolve_uvars = false in
    push_subst_aux resolve_uvars s t
  | _ -> t

(* compress:
      This is used pervasively, throughout the codebase

      The recommended use for inspecting a term
      is to first call compress on it, which should
         1. push delayed substitutions down one level

         2. eliminate any top-level (Tm_uvar uv) node,
            when uv has been assigned a solution already

      `compress` should will *not* memoize the result of uvar
      solutions (since those could be reverted), nor the result
      of `push_subst` (since it internally uses the unionfind
      graph too).

      The function is broken into a fast-path where the
      result can be easily determined and a recursive slow
      path.

      Warning: if force_uvar changes to operate on inputs other than
      Tm_uvar then the fastpath out match in compress will need to be
      updated.

      This function should NEVER return a Tm_delayed. If you do any
      non-trivial change to it, it would be wise to uncomment the check
      below and run a full regression build.
*)
let rec compress_slow (t:term) =
    let t = force_uvar t in
    match t.n with
    | Tm_delayed {tm=t'; substs=s} ->
        compress (push_subst s t')
    | _ ->
        t
and compress (t:term) =
  match t.n with
    | Tm_delayed _ | Tm_uvar _ ->
        let r = compress_slow t in
        (* begin match r.n with *)
        (* | Tm_delayed _ -> failwith "compress attempting to return a Tm_delayed" *)
        (* | _ -> () *)
        (* end; *)
        r
    | _ ->
        t

let subst s t = subst' ([s], NoUseRange) t
let set_use_range r t = subst' ([], SomeUseRange (Range.set_def_range r (Range.use_range r))) t
let subst_comp s t = subst_comp' ([s], NoUseRange) t
let subst_bqual s imp = subst_bqual' ([s], NoUseRange) imp
let subst_aqual s imp = subst_aqual' ([s], NoUseRange) imp
let subst_ascription s (asc:ascription) = subst_ascription' ([s], NoUseRange) asc
let subst_decreasing_order s dec = subst_dec_order' ([s], NoUseRange) dec
let subst_residual_comp s rc =
  match rc.residual_typ with
  | None -> rc
  | Some t -> {rc with residual_typ=subst s t |> Some}
let closing_subst (bs:binders) =
    List.fold_right (fun b (subst, n)  -> (NM(b.binder_bv, n)::subst, n+1)) bs ([], 0) |> fst
let open_binders' bs =
   let rec aux bs o = match bs with
        | [] -> [], o
        | b::bs' ->
          let x' = {freshen_bv b.binder_bv with sort=subst o b.binder_bv.sort} in
          let imp = subst_bqual o b.binder_qual in
          let attrs = b.binder_attrs |> List.map (subst o) in
          let o = DB(0, x')::shift_subst 1 o in
          let bs', o = aux bs' o in
          (S.mk_binder_with_attrs x' imp b.binder_positivity attrs)::bs', o in
   aux bs []
let open_binders (bs:binders) = fst (open_binders' bs)
let open_term' (bs:binders) t =
   let bs', opening = open_binders' bs in
   bs', subst opening t, opening
let open_term (bs:binders) t =
   let b, t, _ = open_term' bs t in
   b, t
let open_comp (bs:binders) t =
   let bs', opening = open_binders' bs in
   bs', subst_comp opening t
let open_ascription bs asc =
  let bs', opening = open_binders' bs in
  bs', subst_ascription opening asc

let open_pat (p:pat) : pat & subst_t =
    let rec open_pat_aux sub p =
        match p.v with
        | Pat_constant _ -> p, sub

        | Pat_cons(fv, us_opt, pats) ->
            let us_opt = subst_univs_opt [sub] us_opt in
            let pats, sub = pats |> List.fold_left (fun (pats, sub) (p, imp) ->
                let p, sub = open_pat_aux sub p in
                ((p,imp)::pats, sub)) ([], sub) in
            {p with v=Pat_cons(fv, us_opt, List.rev pats)}, sub

        | Pat_var x ->
            let x' = {freshen_bv x with sort=subst sub x.sort} in
            let sub = DB(0, x')::shift_subst 1 sub in
            {p with v=Pat_var x'}, sub

        | Pat_dot_term eopt ->
            let eopt = Option.map (subst sub) eopt in
            {p with v=Pat_dot_term eopt}, sub
    in
    open_pat_aux [] p

let open_branch' (p, wopt, e) =
    let p, opening = open_pat p in
    let wopt = match wopt with
        | None -> None
        | Some w -> Some (subst opening w) in
    let e = subst opening e in
    (p, wopt, e), opening

let open_branch br =
    let br, _ = open_branch' br in
    br

let close (bs:binders) t = subst (closing_subst bs) t
let close_comp (bs:binders) (c:comp) = subst_comp (closing_subst bs) c
let close_binders (bs:binders) : binders =
    let rec aux s (bs:binders) = match bs with
        | [] -> []
        | b::tl ->
          let x = {b.binder_bv with sort=subst s b.binder_bv.sort} in
          let imp = subst_bqual s b.binder_qual in
          let attrs = b.binder_attrs |> List.map (subst s) in
          let s' = NM(x, 0)::shift_subst 1 s in
          (S.mk_binder_with_attrs x imp b.binder_positivity attrs)::aux s' tl in
    aux [] bs
let close_ascription (bs:binders) (asc:ascription) =
  subst_ascription (closing_subst bs) asc

let close_pat p =
    let rec aux sub p = match p.v with
       | Pat_constant _ -> p, sub

       | Pat_cons(fv, us_opt, pats) ->
         let us_opt = subst_univs_opt [sub] us_opt in         
         let pats, sub = pats |> List.fold_left (fun (pats, sub) (p, imp) ->
             let p, sub = aux sub p in
             ((p,imp)::pats, sub)) ([], sub) in
         {p with v=Pat_cons(fv, us_opt, List.rev pats)}, sub

       | Pat_var x ->
         let x = {x with sort=subst sub x.sort} in
         let sub = NM(x, 0)::shift_subst 1 sub in
         {p with v=Pat_var x}, sub

       | Pat_dot_term eopt ->
         let eopt = Option.map (subst sub) eopt in
         {p with v=Pat_dot_term eopt}, sub in
    aux [] p

let close_branch (p, wopt, e) =
    let p, closing = close_pat p in
    let wopt = match wopt with
        | None -> None
        | Some w -> Some (subst closing w) in
    let e = subst closing e in
    (p, wopt, e)

let univ_var_opening (us:univ_names) =
    let n = List.length us - 1 in
    let s = us |> List.mapi (fun i u -> UN(n - i, U_name u)) in
    s, us

let univ_var_closing (us:univ_names) =
    let n = List.length us - 1 in
    us |> List.mapi (fun i u -> UD(u, n - i))

let open_univ_vars  (us:univ_names) (t:term)  : univ_names & term =
    let s, us' = univ_var_opening us in
    let t = subst s t in
    us', t

let open_univ_vars_comp (us:univ_names) (c:comp) : univ_names & comp =
    let s, us' = univ_var_opening us in
    us', subst_comp s c

let close_univ_vars (us:univ_names) (t:term) : term =
    let s = univ_var_closing us in
    subst s t

let close_univ_vars_comp (us:univ_names) (c:comp) : comp =
    let n = List.length us - 1 in
    let s = us |> List.mapi (fun i u -> UD(u, n - i)) in
    subst_comp s c

let open_let_rec lbs (t:term) =
    let n_let_recs, lbs, let_rec_opening =
      if is_top_level lbs
      then 0, lbs, []  //top-level let recs are not opened,
                       //but we still have to open their universe binders,
                       //if any (see below)
      else List.fold_right
              (fun lb (i, lbs, out) ->
                 let x = Syntax.freshen_bv (Inl?.v lb.lbname) in
                 i+1, {lb with lbname=Inl x}::lbs, DB(i, x)::out)
              lbs
              (0, [], [])
    in
      (* Consider
                let rec f<u> x = g x
                and g<u> y = f y in
                f 0, g 0
            In de Bruijn notation, this is
                let rec f x = g@1 x@0
                and g y = f@2 y@0 in
                f@1 0, g@0 0
            i.e., the recursive environment for f is, in order:
                        u, f, g, x
                  for g is
                        u, f, g, y
                  and for the body is
                        f, g

         See FStar.Util.check_mutual_universes
           - We maintain an invariant that all the letbindings
             in a mutually recursive nest abstract over the
             same sequence of universes
         *)
    let _, us, u_let_rec_opening =
        List.fold_right
             (fun u (i, us, out) ->
                  let u = Syntax.new_univ_name None in
                  i+1, u::us, UN(i, U_name u)::out)
             (List.hd lbs).lbunivs
             (n_let_recs, [], let_rec_opening)
    in
    let lbs = lbs |> List.map (fun lb ->
        {lb with lbunivs=us;
                 lbdef=subst u_let_rec_opening lb.lbdef;
                 lbtyp=subst u_let_rec_opening lb.lbtyp})
    in
    let t = subst let_rec_opening t in
    lbs, t

let close_let_rec lbs (t:term) =
    let n_let_recs, let_rec_closing =
      if is_top_level lbs
      then 0, [] //top-level let recs do not have to be closed
                 //except for their universe binders, if any (see below)
      else List.fold_right
               (fun lb (i, out) -> i+1, NM(Inl?.v lb.lbname, i)::out)
               lbs
               (0, [])
    in
    let _, u_let_rec_closing =
        List.fold_right
          (fun u (i, out) -> i+1, UD(u, i)::out)
          (List.hd lbs).lbunivs
          (n_let_recs, let_rec_closing)
    in
    let lbs = lbs |> List.map (fun lb ->
           {lb with lbdef=subst u_let_rec_closing lb.lbdef;
                    lbtyp=subst u_let_rec_closing lb.lbtyp})
    in
    let t = subst let_rec_closing t in
    lbs, t

let close_tscheme (binders:binders) ((us, t) : tscheme) =
    let n = List.length binders - 1 in
    let k = List.length us in
    let s = List.mapi (fun i b -> NM(b.binder_bv, k + (n - i))) binders in
    let t = subst s t in
    (us, t)

let close_univ_vars_tscheme (us:univ_names) ((us', t):tscheme) =
   let n  = List.length us - 1 in
   let k = List.length us' in
   let s = List.mapi (fun i x -> UD(x, k + (n - i))) us in
   (us', subst s t)

let subst_tscheme (s:list subst_elt) ((us, t):tscheme) =
    let s = shift_subst (List.length us) s in
    (us, subst s t)

let opening_of_binders (bs:binders) =
  let n = List.length bs - 1 in
  bs |> List.mapi (fun i b -> DB(n - i, b.binder_bv))

let closing_of_binders (bs:binders) = closing_subst bs

let open_term_1 b t =
    match open_term [b] t with
    | [b], t -> b, t
    | _ -> failwith "impossible: open_term_1"

let open_term_bvs bvs t =
    let bs, t = open_term (List.map mk_binder bvs) t in
    List.map (fun b -> b.binder_bv) bs, t

let open_term_bv bv t =
    match open_term_bvs [bv] t with
    | [bv], t -> bv, t
    | _ -> failwith "impossible: open_term_bv"
