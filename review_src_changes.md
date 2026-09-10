
+(* [has_type] is universe-polymorphic in both the type of [x] and in [t'].
+   Callers that only build a formula for the SMT encoder, which erases
+   universes, may use these [u#0]s; a caller that builds a term to be
+   re-typechecked must use [mk_has_type_us] with the real universes. *)
+let mk_has_type t x t' = mk_has_type_us [U_zero; U_zero] t x t'


Does comp_typ need a univs any more? It is always just the universe of the
result type. And like other primitive universe-polymorphic type formers (e.g.,
->), we could treat comp_typ the same way. 

NBETerm still has the following. It can be simplified to just comp_typ, and also
does not need comp_univs

and comp =
  | Tot of t
  | GTot of t
  | Comp of comp_typ

and comp_typ = {
  comp_univs:universes;
  effect_name:lident;
  result_typ:t;
  flags:list cflag
}


What is the role of residual_comp. Do we really still need it? Can it be
simplified further, e.g., just to an effect name? Or do we need it at all? The
smt encoding uses it---check.

(* Residual of a computation type after typechecking *)
and residual_comp = {
    residual_effect:lident;                (* first component is the effect name *)
    residual_typ   :option typ;           (* second component: result type *)
    residual_flags :list cflag            (* third component: contains (an approximation of) the cflags *)
}


+        (* [x:t{x == e}] is inhabited by [e] whenever [t] is.  That singleton
+           shape is what [assume_result_eq_pure_term] gives the result type of a
+           pure term now that a computation has no postcondition to record it
+           in, so it turns up on the result type of any definition ending in a
+           literal. *)
+        | Tm_refine {b; phi} when clearly_inhabited b.sort ->
+            let bv, phi = SS.open_term_bv b phi in
+            let is_name (t:term) : ML bool =
+              match (SS.compress t).n with
+              | Tm_name bv' -> S.bv_eq bv bv'
+              | _ -> false in
+            let hd, args = U.head_and_args_full phi in
+            (match (U.un_uinst hd).n, args with
+             | Tm_fvar fv, [_; (lhs, _); (rhs, _)]
+                 when S.fv_eq_lid fv PC.eq2_lid ->
+               (is_name lhs && not (FStarC.Class.Setlike.mem bv (Free.names rhs))) ||
+               (is_name rhs && not (FStarC.Class.Setlike.mem bv (Free.names lhs)))
+             | _ -> false)


This should be simplified now, since ghost terms in the typechecker should always have effect name GTot and pure terms should always be Tot, right?

let downgrade_ghost_effect_name l =
    if Ident.lid_equals l PC.effect_Ghost_lid
    then Some PC.effect_Pure_lid
    else if Ident.lid_equals l PC.effect_GTot_lid
    then Some PC.effect_Tot_lid
    else if Ident.lid_equals l PC.effect_GHOST_lid
    then Some PC.effect_PURE_lid
    else None

let ghost_to_pure_aux env non_informative_only c =
         then let ct =
                  match downgrade_ghost_effect_name ct.effect_name with
                  | Some pure_eff ->
-                   let flags = if Ident.lid_equals pure_eff PC.effect_Tot_lid then TOTAL::ct.flags else ct.flags in
-                   {ct with effect_name=pure_eff; flags=flags}
+                   {ct with effect_name=pure_eff}
                  | None ->
-                    let ct = unfold_effect_abbrev env c in //must be GHOST
-                    {ct with effect_name=PC.effect_PURE_lid} in
+                    let ct = unfold_effect_abbrev env c in //must be ghost
+                    {ct with effect_name=PC.primitive_pure_lid} in
              {c with n=Comp ct}
         else c

There's also more confusion like this. Why can't we simplify such checks to just
checking that ct.effect_name is total. Consolidate on a single set of abstract
helper functions to decide if a comp is total, ghost, div, etc, and use it
everywhere, systematically.

+++ b/src/typechecker/FStarC.TypeChecker.Rel.fst
@@ -1544,7 +1544,9 @@ let compress_cprob wl p : ML _
   =
   let whnf_c env c =
     match c.n with
-    | Total ty -> S.mk_Total (whnf env ty)
+    | Comp ct when U.is_bare_tot_or_gtot_comp c
+                && Ident.lid_equals ct.effect_name PC.effect_Tot_lid ->
+      S.mk_Total (whnf env ct.result_typ)
     | _ -> c
   in

Just delete effect_args rather than carrying around this debt:

+       (* A computation type carries no logical content any more, so it has no
+          effect arguments to consider. *)
+       let effect_args : list arg = [] in

ToSyntax.comp_requires: This is ugly code
It would be much cleaner and more readable to destruct on the shape of the terms.
It would also be nicer to make it share the logic present in desugar_comp, to ensure they do not drift
Something like (in pseudo-code)

match destruct_comp t with
| "Lemma", [ Untagged e ] -> ..
| "Lemma", Ensures e::maybe_smt_pats_and_decreases -> ..
| "Lemma", Requires e1::Ensures e2::maybe_smt_pats_and_decreases -> Some (e1, construct_comp "Lemma" [Requires true; Ensures e2]@maybe_smt_pats_and_decreases)
| eff_name, [Untagged result_type; Requires pre; Ensures post ] -> Some (pre, construct_comp eff_name [Requires true; Ensures post])
| _, [Untagged result_type] -> None
...


Why is this necessary? We already have code in place to drop conjuncts in inferred types that mention variables that might escape their scope.

-                let args, aqs = List.map (fun (t, imp) ->
-                  let te, aq = desugar_term_aq env t in
-                  arg_withimp_t imp te, aq) args |> List.unzip in
+                (* The element type is given explicitly: inferring it makes
+                   the result type of the lambda -- which carries the [==] fact
+                   for the pair, mentioning [te] -- the solution of a unification
+                   variable bound outside the lambda. *)
+                let args, aqs =
+                  List.map #_ #(S.arg & antiquotations_temp)
+                    (fun (t, imp) ->
+                      let te, aq = desugar_term_aq env t in
+                      arg_withimp_t imp te, aq)
+                    args
+                  |> List.unzip in


We should reject universe annotations on effects, rather than accepting
something the user wrote and then silently dropping it.

@@ -2291,9 +2426,13 @@ and desugar_comp r (allow_type_promotion:bool) env t : ML _ =
     let (eff, cattributes), args = pre_process_comp_typ t in
     if Nil? args then
       fail Errors.Fatal_NotEnoughArgsToEffect (Format.fmt1 "Not enough args to effect %s" (show eff));
+    (* An explicit universe application on an effect, as in [Tot u#0 int], is
+       accepted and discarded: a computation is an effect name applied to its
+       result type alone, so its universe is that of the result type and there
+       is nowhere left to record an annotation -- nor anything it could say
+       that the result type does not already. *)
     let is_universe (_, imp) = imp = UnivApp in

Remove this comment. It is no longer relevant

 (* The postcondition for Lemma is thunked, to allow to assume the precondition
         * (c.f. #57), so add the thunking here *)

See this code in ToSyntax. In what case do we have attributes in the last arg of an effect abbreviation?

    let qlid = qualify env id in
        let se =
            if quals |> List.contains S.Effect
            then
                let t, cattributes =
                    match (unparen t).tm with
                        (* TODO : we are only handling the case Effect args (attributes ...) *)
                        | Construct (head, args) ->
                            let cattributes, args =
                                match List.rev args with
                                    | (last_arg, _) :: args_rev ->
                                        begin match (unparen last_arg).tm with
                                            | Attributes ts -> ts, List.rev (args_rev)
                                            | _ -> [], args
                                        end
                                    | _ -> [], args
                            in
                            mk_term (Construct (head, args)) t.range t.level,
                            desugar_attributes env cattributes
                         | _ -> t, []
                 in

Why don't we desugar the effect name to the root effect name at this stage in ToSyntax? 
We have already desugared away the pre & postcondition. Why not the name also?
        
@@ -2403,12 +2544,16 @@ and desugar_comp r (allow_type_promotion:bool) env t : ML _ =
       let flags = flags @ decreases_clause @ (match smtpat with
                                               | None -> []
                                               | Some p -> [SMTPAT p]) in
-      mk_Comp ({comp_univs=universes;
-                effect_name=eff;
+      (* A computation type carries no specification: the postcondition becomes
+         a property of the result type, and the precondition is handed back to
+         the caller, which turns it into an implicit [squash] binder (arrow
+         codomain) or an assertion (ascription).  See
+         [Syntax.Util.refine_with_post]. *)
+      let result_typ = U.refine_with_post result_typ post in
+      mk_Comp ({effect_name=eff;
                 result_typ=result_typ;
-                comp_pre=pre;
-                comp_post=post;
-                flags=flags})
+                flags=flags}),
+      pre

We are making breaking changes anyway. We should insist on sub-effect relations written between
the root effects rather than between abbreviations, rather than accomodating it with this hack

   | SubEffect l ->
-    let src_ed = lookup_effect_lid env l.msource d.drange in
-    let dst_ed = lookup_effect_lid env l.mdest d.drange in
+    let src_ed = lookup_effect_lid_unfold env l.msource d.drange in
+    let dst_ed = lookup_effect_lid_unfold env l.mdest d.drange in
     let lift =
