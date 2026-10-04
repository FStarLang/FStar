module Phase2CoreBranchTypeByUnfolding

(* [pfr f] against [ct k] for a recursive [ct]: [pfr] unfolds to a
   refinement whose base type never comes to match [ct k], so Core states
   the guard on the folded terms, [pfr f == ct k], provable from the
   equations of [ct] under [k == R f], rather than on the refinement, whose
   encoding is unrelated to that of [pfr]'s body (everparse
   ASN1.Spec.Interpreter). *)

let pfr (#t:Type) (f: t -> bool) = x:t{f x == true}
noeq type kk = | T : nat -> kk | R : (int -> bool) -> kk
#push-options "--warn_error -328"
let rec ct (k:kk) : Type0 = match k with | T _ -> int | R f -> pfr #int f
#pop-options
let parser (t:Type) = int -> option (t & nat)
assume val mk (f: int -> bool) : parser (pfr #int f)
assume val mkt : parser int

let foo (k:kk) : parser (ct k) =
  match k with
  | R f -> mk f
  | T _ -> mkt
