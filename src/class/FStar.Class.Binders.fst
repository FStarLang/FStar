module FStar.Class.Binders

open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.Range
open FStar.Compiler.Util
open FStar.Compiler.Set
open FStar.Syntax.Syntax
module F = FStar.Syntax.Free
open FStar.Errors
open FStar.Errors.Msg

instance hasNames_term : hasNames term = {
  freeNames = F.names;
}

instance hasNames_comp : hasNames comp = {
  freeNames = (fun c -> match c.n with
               | Total t
               | GTotal t -> F.names t
               | Comp ct -> List.fold_left Set.union (Set.empty ())
                             (F.names ct.result_typ :: (List.map (fun (a,_) -> F.names a) ct.effect_args)))
}

instance hasBinders_list_bv = {
  boundNames = Set.from_list;
}

instance hasBinders_set_bv = {
  boundNames = id;
}
