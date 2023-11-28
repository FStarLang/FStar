module FStar.Class.Binders

open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.Range
open FStar.Compiler.Util
open FStar.Syntax.Syntax
module F = FStar.Syntax.Free
open FStar.Errors
open FStar.Errors.Msg

val set_join : l:(list (set 'a)){Cons? l} -> set 'a
let set_join (hd::tl) = List.fold_left set_union hd tl

instance hasNames_term : hasNames term = {
  freeNames = F.names;
}

instance hasNames_comp : hasNames comp = {
  freeNames = (fun c -> match c.n with
               | Total t
               | GTotal t -> F.names t
               | Comp ct -> set_join (F.names ct.result_typ :: (List.map (fun (a,_) -> F.names a) ct.effect_args)))
}

instance hasBinders_list_bv = {
  boundNames = (fun l -> as_set l order_bv);
}

instance hasBinders_set_bv = {
  boundNames = id;
}
