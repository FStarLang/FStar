module FStar.Tactics.V2.SyntaxCoercions

open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.NamedView
open FStar.Sealed

[@@coercion]
let namedv_to_term (x : namedv) : Tot term =
  pack (Tv_Var x)

[@@coercion]
let binder_to_namedv (b : binder) : Tot namedv =
  {
    ppname = b.ppname;
    uniq   = b.uniq;
    sort   = seal b.sort;
  }

[@@coercion]
let binder_to_term (b : binder) : Tot term =
  pack (Tv_Var (binder_to_namedv b))

[@@coercion]
let binding_to_namedv (b : binding) : Tot namedv =
  {
    ppname = b.ppname;
    sort   = seal b.sort;
    uniq   = b.uniq
  }

[@@coercion]
let binding_to_term (x : binding) : Tot term =
  namedv_to_term (binding_to_namedv x)
