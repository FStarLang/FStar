(*--build-config
    options:--warn_top_level_effects --admit_fsi FStar.Squash --admit_fsi FStar.Set --print_implicits;
    other-files:constr.fst squash.fsti set.fsi heap.fst st.fst all.fst;
--*)
module FStar.SquashProperties

open FStar.Constructive

open FStar.Squash

val join_squash : #a:Type -> squash (squash a) -> Tot (squash a)
let join_squash (a:Type) s = bind_squash #(squash a) #a s (fun x -> x)

val squash_arrow : #a:Type -> #p:(a -> Type) ->
  =f:(x:a -> Tot (squash (p x))) -> Tot (squash (x:a -> Tot (p x)))
let squash_arrow (a:Type) (p:(a->Type)) f =
  squash_double_arrow (return_squash (fun x -> f x))

val forall_intro : #a:Type -> #p:(a -> Type) ->
  =f:(x:a -> Lemma (p x)) -> Lemma (x:a -> Tot (p x))(* (forall (x:a). p x) *)
let forall_intro (a:Type) (p:(a->Type)) f =
  let ff : (x:a -> Tot (squash (p x))) = (fun x -> f x; get_proof (p x)) in
  give_proof #(x:a -> Tot (p x)) (squash_arrow #a #p ff)


// currently unused
// val squash_elim : a:Type -> #b:Type -> t1:b -> t2:b ->
//       (       a -> Tot (ceq t1 t2)) ->
//   Tot (squash a -> Tot (ceq t1 t2))

(* assume val tt (t:Type) : squash t *)

(* assume val squash_mem_elim : a:Type -> #b:Type -> t1:b -> t2:b -> *)
(*       (x:squash a -> t:(squash a -> Type) -> Tot (t ())) -> *)
(*   Tot (x:squash a -> t:(squash a -> Type) -> Tot (t x)) *)

(* get_proof and give_proof are phrased in terms of squash *)

(* The whole point of defining squash is to soundly allow define excluded_middle;
   here this follows from get_proof and give_proof *)

val bool_of_or : #p:Type -> #q:Type -> (p \/ q) -> 
  Tot (b:bool{(b ==> p) /\ (not(b) ==> q)})
let bool_of_or (p:Type) (q:Type) (t:p \/ q) = 
  match t with
  | Left  _ -> true
  | Right _ -> false

val excluded_middle : p:Type -> Tot (squash (b:bool{b <==> p}))
let excluded_middle (p:Type) = map_squash (get_proof (p \/ ~p)) bool_of_or 

val excluded_middle_squash : p:Type -> Tot (squash (cor p (cnot p)))
let excluded_middle_squash (p:Type) =
  bind_squash (excluded_middle p) (fun x ->
  if x then
    map_squash (get_proof p) IntroL
  else
    return_squash (IntroR (fun (h:p) -> give_proof (return_squash h); false_elim ())))

(* we thought we might prove proof irrelevance by Berardi ... but didn't manage *)

(* Conditional on any Type -- unused below *)
val ifProp: #p:Type -> b:Type -> (e1:squash p) -> (e2:squash p) -> Tot (squash p)
let ifProp (#p:Type) (b:Type) e1 e2 =
   bind_squash (excluded_middle_squash b) (fun x ->
   match x with
   | IntroL _ -> e1
   | IntroR _ -> e2)

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


val l1: (a:Type) -> (b:Type) -> Tot (squash (retract_cond (pow a) (pow b)))
let l1 (a:Type) (b:Type) = 
   map_squash (excluded_middle_squash (retract (pow a) (pow b))) (fun x ->
   match x with
   | IntroL (MkR f0 g0 e) -> MkC f0 g0 (fun _ -> e)
   | IntroR nr ->
    let f0 (x:pow a) (y:b) = false in
     let g0 (x:pow b) (y:a) = false in
     MkC f0 g0 (fun r -> cfalse_elim (nr r)))

(* The paradoxical set *)
type U = p:Type -> Tot (squash (pow p))

(* Bijection between U and (pow U) *)
val f : U -> Tot (squash (pow U))
let f u = u U

val g : squash (pow U) -> Tot U
let g sh = fun (x:Type) -> 
  let (slX:squash (pow U -> Tot (pow x))) = map_squash (l1 x U) MkC.j2 in 
  let (srU:squash (pow U -> Tot (pow U))) = map_squash (l1 U U) MkC.i2 in 
  bind_squash srU (fun rU ->
  bind_squash slX (fun lX ->
  bind_squash sh (fun h ->
  return_squash (lX (rU h)))))

(* This only works if importing all.fst, which is nonsense *)
val r : U
let r =
  let ff : (U -> Tot (squash bool)) =
      (fun (u:U) -> map_squash (u U) (fun uu -> not (uu u))) in
  g (squash_arrow ff)

(* CH: stopped here *)
(* val not_has_fixpoint : squash (ceq (r U r) (not (r U r))) *)
(* let not_has_fixpoint = Refl #bool #(r U r) *)


(* otherwise we could assume proof irrelevance as an axiom;
   note that proof relevance shouldn't be derivable for squash types *)
(* val not_provable : unit -> *)
(*   Tot (cnot (ceq (return_squash true) (return_squash false))) *)
(* val not_provable : unit -> *)
(*   Tot (squash (cnot (ceq (return_squash true) (return_squash false)))) *)

type cheq (#a:Type) (x:a) : #b:Type -> b -> Type =
  | HRefl : cheq #a x #a x

(* val not_provable : unit -> *)
(*   Tot (cimp (cheq (return_squash #(b:bool{b=true})  true) *)
(*                   (return_squash #(b:bool{b=false}) false)) (squash cfalse)) *)
(* let not_provable () = *)
(*   (fun h -> match h with *)
(*             | HRefl ->  *)
(*               assert(return_squash #(b:bool{b=true}) true == *)
(*                      return_squash #(b:bool{b=false}) false); *)
(*               bind_squash (return_squash #(b:bool{b=true})  true) (fun btrue -> *)
(*               bind_squash (return_squash #(b:bool{b=false}) false) (fun bfalse -> *)
(*               assert (btrue <> bfalse); magic()))) *)

(* TODO:
  - play with this a bit more; try out some examples
    + search for give_proof / get_proof
*)
