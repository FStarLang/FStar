module FStar.Cardinality.Universes

open FStar.Functions
open FStar.Cardinality.Cantor

(* This type is an injection of all powersets of Type u (i.e. Type u -> bool
functions) into Type (u+1) *)
noeq
type type_powerset : (Type u#a -> bool) -> Type u#(max (a+1) b) =
  | Mk : f:(Type u#a -> bool) -> type_powerset f

let aux_inj_type_powerset (f1 f2 : powerset (Type u#a))
  : Lemma (requires type_powerset u#a u#b f1 == type_powerset u#a u#b f2)
          (ensures f1 == f2)
=
  assert (type_powerset f1 == type_powerset f2);
  let xx1 : type_powerset f1 = Mk f1 in
  let xx2 : type_powerset f2 = coerce_eq () xx1 in
  assert (xx1 === xx2);
  assert (f1 == f2)
  
let inj_type_powerset () : Lemma (is_inj type_powerset) =
  Classical.forall_intro_2 (fun f1 -> Classical.move_requires (aux_inj_type_powerset f1))
 
(* let u' > u be universes. (u' = max(a+1, b), u=a below)
   The general structure of this proof is:
   1- We know there is an injection of powerset(Type(u)) into Type(u') (see type_powerset above)
   2- We know there is NO injection from powerset(Type(u)) into Type(u) (see no_inj_powerset)
   3- Therefore, there cannot be an injection from Type(u') into Type(u), otherwise we would
      compose it with the first injection and obtain the second impossible injection.
*)
let no_inj_universes (f : Type u#(max (a+1) b) -> Type u#a) : Lemma (~(is_inj f)) =
  let aux () : Lemma (requires is_inj f) (ensures False) =
    let comp : powerset (Type u#a) -> Type u#a = fun x -> f (type_powerset x) in
    inj_type_powerset ();
    inj_comp type_powerset f;
    no_inj_powerset _ comp
  in
  Classical.move_requires aux ()

let no_inj_universes_suc (f : Type u#(a+1) -> Type u#a) : Lemma (~(is_inj f)) =
  no_inj_universes f
