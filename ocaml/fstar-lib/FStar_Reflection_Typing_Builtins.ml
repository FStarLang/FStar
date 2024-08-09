open FStar_Syntax_Syntax
open FStar_Reflection_Types
module R = FStar_Compiler_Range

let dummy_range = R.dummyRange
let underscore = FStar_Ident.mk_ident ("_", R.dummyRange)
let int_as_bv (n:Prims.int) = { ppname = underscore; index = n; sort = tun}

let open_term (t:term) (v:Prims.int)
  : term
  = let subst = DB (Z.zero, int_as_bv v) in
    FStar_Syntax_Subst.subst [subst] t

let close_term (t:term) (v:Prims.int)
  : term
  = let subst = NM (int_as_bv v, Z.zero) in
    FStar_Syntax_Subst.subst [subst] t

let open_with (t:term) (v:term)
  : term
  = let neg = int_as_bv (Z.of_int (-1)) in (* a temporary non-clashing name *)
    let opened_t = FStar_Syntax_Subst.subst [DB(Z.zero, neg)] t in
    (* gets substituted away immediately *)
    FStar_Syntax_Subst.subst [NT(neg, v)] opened_t

let rename (t:term) (x:Prims.int) (y:Prims.int)
  : term
  = FStar_Syntax_Subst.subst [NT(int_as_bv x, bv_to_name (int_as_bv y))] t


  
