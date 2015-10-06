(*--build-config
    options:--warn_top_level_effects --admit_fsi FStar.Set --admit_fsi FStar.Map --verify_module Berardi;
    other-files:constr.fst ext.fst classical.fst set.fsi heap.fst map.fsi st.fst all.fst;
--*)
module Berardi

open FStar.Constructive
open FStar.Classical

(* Berardi's paradox:
   https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Berardi.html
   This was brought to our attention by Maxime Denes.
*)

(* Ingredient #1: impredicative polymorphism in Type, as in *)
type t = a:Type -> Tot a
val foo : t -> Tot t
let foo f = f t

(* Ingredient #2: excluded middle in Type *)
// assume val cem : a:Type -> Tot (cor a (cnot a))

(* Alternative Ingredient #2: proof reification to Type *)

assume val get_proof : p:Type -> Pure p (requires p) (ensures (fun _ -> True))

val bool_of_or : #p:Type -> #q:Type -> (p \/ q) -> 
  Tot (b:bool{(b ==> p) /\ (not(b) ==> q)})
let bool_of_or (p:Type) (q:Type) (t:p \/ q) = 
  match t with
  | Left  _ -> true
  | Right _ -> false

val excluded_middle : p:Type -> Tot (b:bool{b <==> p})
let excluded_middle (p:Type) = bool_of_or (get_proof (p \/ ~p))

val cem : p:Type -> Tot (cor p (cnot p))
let cem (p:Type) = 
  if excluded_middle p then
    IntroL (get_proof p)
  else
    IntroR (fun (h:p) -> give_proof h; false_elim ())

(* Conditional on any Type -- unused below *)
val ifProp: #p:Type -> b:Type -> (e1:p) -> (e2:p) -> Tot p
let ifProp (#p:Type) (b:Type) e1 e2 =
   match cem b with
   | IntroL _ -> e1
   | IntroR _ -> e2

(* Axiom of choice applied to constructive disjunction -- unused below *)
val ac_if: p:Type -> b:Type -> e1:p -> e2:p -> q:(p -> Type) ->
  (b -> Tot (q e1)) -> (cnot b -> Tot (q e2)) -> Tot (q (ifProp b e1 e2))
let ac_if (p:Type) (b:Type) e1 e2 (q:(p -> Type)) l r =
   match cem b with
   | IntroL w -> l w 
   | IntroR w -> r w


(* The powerset operator *)
type pow (p:Type) = p -> Tot bool

type retract 'a 'b : Type =
  | MkR: i:('a -> Tot 'b) -> 
         j:('b -> Tot 'a) ->
         inv:(x:'a -> Tot (ceq (j (i x)) x)) -> 
         retract 'a 'b 

type retract_cond 'a 'b : Type =
  | MkC: i2:('a -> Tot 'b) -> 
         j2:('b -> Tot 'a) -> 
         inv2:(retract 'a 'b -> x:'a -> Tot (ceq (j2 (i2 x)) x)) -> 
         retract_cond 'a 'b 

(* unused below *)
val ac: r:retract_cond 'a 'b -> retract 'a 'b -> x:'a ->
          Tot (ceq ((MkC.j2 r) (MkC.i2 r x)) x)
let ac (MkC _ _ inv2) = inv2

val l1: (a:Type) -> (b:Type) -> Tot (retract_cond (pow a) (pow b))
let l1 (a:Type) (b:Type) = 
   match cem (retract (pow a) (pow b)) with
   | IntroL (MkR f0 g0 e) -> MkC f0 g0 (fun _ -> e)
   | IntroR nr ->
     let f0 (x:pow a) (y:b) = false in
     let g0 (x:pow b) (y:a) = false in
     MkC f0 g0 (fun r -> cfalse_elim (nr r))


(* The paradoxical set *)
type U = p:Type -> Tot (pow p)

(* Bijection between U and (pow U) *)
val f : U -> Tot (pow U)
let f u = u U

val g : pow U -> Tot U
let g (h:pow U) = fun (x:Type) -> 
  let lX:(pow U -> Tot (pow x)) = MkC.j2 (l1 x U) in 
  let rU:(pow U -> Tot (pow U)) = MkC.i2 (l1 U U) in 
  lX (rU h)


(* The set of elements not belonging to itself *)
val r : U
let r = g (fun (u:U) -> not (u U u))

(* Russell's  paradox *)
val not_has_fixpoint : ceq (r U r) (not (r U r))
let not_has_fixpoint = Refl #bool #(r U r)

(* Contradiction *)
val contradict : unit -> Lemma False
let contradict () = ignore (not_has_fixpoint)
