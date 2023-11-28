module FStar.Class.Binders

open FStar.Compiler.Util
open FStar.Syntax.Syntax

class hasNames (a:Type) = {
  freeNames : a -> set bv;
}

class hasBinders (a:Type) = {
  boundNames : a -> set bv;
}

instance val hasNames_term : hasNames term
instance val hasNames_comp : hasNames comp

instance val hasBinders_list_bv : hasBinders (list bv)
instance val hasBinders_set_bv  : hasBinders (set bv)
