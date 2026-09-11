
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
