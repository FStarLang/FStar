module FStar.Class.Binders

open FStar.Compiler.Util
open FStar.Compiler.FlatSet
open FStar.Syntax.Syntax

(* TODO: should be for any setlike *)
class hasNames (a:Type) = {
  freeNames : a -> flat_set bv;
}

class hasBinders (a:Type) = {
  boundNames : a -> flat_set bv;
}

instance val hasNames_term : hasNames term
instance val hasNames_comp : hasNames comp

instance val hasBinders_list_bv : hasBinders (list bv)
instance val hasBinders_set_bv  : hasBinders (flat_set bv)
