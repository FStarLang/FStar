Why do we still need this?

(* A computation with a trivial specification: [mk_triv_comp eff t flags] *)
+val mk_triv_comp :  lident -> typ -> list cflag -> ML comp

This looks unsafe/type incorrect. SMT endoding does not erase universes any more


+(* [has_type] is universe-polymorphic in both the type of [x] and in [t'].
+   Callers that only build a formula for the SMT encoder, which erases
+   universes, may use these [u#0]s; a caller that builds a term to be
+   re-typechecked must use [mk_has_type_us] with the real universes. *)
+let mk_has_type t x t' = mk_has_type_us [U_zero; U_zero] t x t'
+
