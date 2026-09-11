module FStarC.Class.Binders

open FStarC
open FStarC.Effect
open FStarC.Range
open FStarC.FlatSet
open FStarC.Syntax.Syntax
module F = FStarC.Syntax.Free
open FStarC.Errors
open FStarC.Errors.Msg

instance hasNames_term : hasNames term = {
  freeNames = F.names;
}

instance hasNames_comp : hasNames comp = {
  freeNames = (fun c -> match c.n with
               | Comp ct -> F.names ct.result_typ)
}

instance hasBinders_list_bv = {
  boundNames = from_list;
}

instance hasBinders_set_bv = {
  boundNames = id;
}
