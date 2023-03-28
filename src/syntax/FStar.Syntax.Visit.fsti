module FStar.Syntax.Visit

open FStar.Syntax.Syntax

(* This is a `map` visitor over terms, `visit f t` returns a version of
`t` "adjusted" by applying `f` on every node. The traversal is bottom up
(and there is no shortcircuit/cancel mechanism). Every `term` included
in `t` is visited and transformed, (function bodies, head and args of
application, binder types, bv sorts, effect args, decreases clauses,
etc). If something is not covered, that is a bug.

NOTE: no binders are opened nor closed in this traversal. The traversal
preserves ranges but discards memoized info (vars and hash_code).

The `f` function should handle only the cases are interesting to it,
defaulting to returning the original term elsewhere. For instance, this
(only slightly ficticious) call

  visit (fun t ->
    match head_and_args t with
    | (Tm_fvar plus, [a1;a2]) where fv_eq_lid plus PC.op_Addition ->
      let n1 = unembed a1 in
      let n2 = unembed a2 in
      mk (Tm_const (C_int n2))

    | (Tm_fvar plus, _) where fv_eq_lid plus PC.op_Addition ->
      raise BadApplication

    | _ -> t
  ) tm

Will fold additions of two constants, raise an exception if the addition
operator is applied to anything but constants, and leave everything else
unchanged. As the traversal is bottom-up, this should fold expressions
like (1+2)+(3+4) in a single call.
*)
val visit_term : (term -> term) -> term -> term

(* As above, but a callback for universes can also be provided that works
in the same manner. In visit_term, it just defaults to the identity. *)
val visit_term_univs : (term -> term) -> (universe -> universe) -> (term -> term)

(* As above, but works on any sigelt, visiting all of its underlying
terms and universes. *)
val visit_sigelt : (term -> term) -> (universe -> universe) -> (sigelt -> sigelt)
