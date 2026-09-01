module UnfoldClass

open FStar.Tactics.V2
open FStar.Tactics.Typeclasses

module L = FStar.List.Tot

(* All fields here are propositional, so F* infers `noeq` for the class. The
`unfold` written by the user must not clash with that inferred qualifier:
refusing the combination would make `unfold class` fail for a reason the
user did not choose. Reduced from Kuiper.Array.Vectorized. *)
inline_for_extraction noextract
unfold
class sized (et : Type) = {
  [@@@no_method] _chunk : nat;
  [@@@no_method] _pf : squash (_chunk == 16);
}

unfold
class uc (a:Type) = {
  um : a -> nat;
}

class pc (a:Type) = {
  pm : a -> nat;
}

instance ui : uc bool = { um = (fun b -> if b then 1 else 0); }
instance pi : pc bool = { pm = (fun b -> if b then 1 else 0); }

(* `unfold` on a class applies to the methods it generates. *)

let method_quals (nm:string) : Tac (list qualifier) =
  match lookup_typ (top_env ()) (explode_qn nm) with
  | None -> fail ("no such name: " ^ nm)
  | Some se -> sigelt_quals se

let is_unfold (q:qualifier) : bool =
  match q with
  | Unfold_for_unification_and_vcgen -> true
  | _ -> false

let _ = assert True by begin
  guard (L.existsb is_unfold (method_quals (`%um)));
  guard (not (L.existsb is_unfold (method_quals (`%pm))))
end

let head_name (t:term) : Tac string =
  match inspect (fst (collect_app t)) with
  | Tv_FVar fv
  | Tv_UInst fv _ -> implode_qn (inspect_fv fv)
  | _ -> fail "head is not an fvar"

(* And it is observable: `delta_qualifier ["unfold"]` turns the method of the
`unfold` class into the projection it stands for, and leaves the other one
alone. *)
let _ = assert True by begin
  let steps = [delta_qualifier ["unfold"]] in
  guard (head_name (norm_term steps (`(um true))) = `%Mkuc?.um);
  guard (head_name (norm_term steps (`(pm true))) = `%pm)
end
