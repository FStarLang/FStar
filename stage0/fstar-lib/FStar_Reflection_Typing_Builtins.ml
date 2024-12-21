open FStarC_Syntax_Syntax
open FStarC_Reflection_Types
module R = FStarC_Compiler_Range

let dummy_range = R.dummyRange
let underscore = FStarC_Ident.mk_ident ("_", R.dummyRange)
let int_as_bv (n:Prims.int) = { ppname = underscore; index = n; sort = tun}

let open_term (t:term) (v:Prims.int)
  : term
  = let subst = DB (Z.zero, int_as_bv v) in
    FStarC_Syntax_Subst.subst [subst] t

let close_term (t:term) (v:Prims.int)
  : term
  = let subst = NM (int_as_bv v, Z.zero) in
    FStarC_Syntax_Subst.subst [subst] t

let open_with (t:term) (v:term)
  : term
  = let neg = int_as_bv (Z.of_int (-1)) in (* a temporary non-clashing name *)
    let opened_t = FStarC_Syntax_Subst.subst [DB(Z.zero, neg)] t in
    (* gets substituted away immediately *)
    FStarC_Syntax_Subst.subst [NT(neg, v)] opened_t

let rename (t:term) (x:Prims.int) (y:Prims.int)
  : term
  = FStarC_Syntax_Subst.subst [NT(int_as_bv x, bv_to_name (int_as_bv y))] t


  
