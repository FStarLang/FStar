module InjectiveTypeFormers
// We need the --__temp_no_proj flag to workaround an F* bug related to generating code for projectors

// F* unfortunately still includes injective type formers;
// these are known to be inconsistent;
// ported inconsistency proof from Lean:
// https://gist.github.com/leodemoura/0c88341bb585bf9a72e6
open FStar.Constructive

(* this file relies on a violation of the cardinality constraints of Type*)
#set-options "--cardinality warn --print_universes --print_bound_var_types"

noeq type i: (Type u#a -> Type u#b) -> Type u#(max (a + 1) (b + 1)) =
| Mk: f:(Type -> Type) -> i f

val injI : x:(Type->Type) -> y:(Type->Type) ->
           Lemma (requires (i x == i y)) (ensures (x == y))
let injI (x:Type->Type) (y:Type->Type) = ()

// Another way to prove injectivity, that doesn't rely on
// projectors for i in the SMT encoding, but does rely
// on inversion and "typing elimination" for Mk
// Namely: that if x : i f then x = Mk e for some e
//    and: that if Mk e : i f then e = f
(*
val injI_ : x:(Type->Type) -> y:(Type->Type) -> i x ->
           Lemma (requires (i x == i y)) (ensures (x == y))
let injI_ (x:Type->Type) (y:Type->Type) ix = ()

val injI : x:(Type->Type) -> y:(Type->Type) ->
           Lemma (requires (i x == i y)) (ensures (x == y))
let injI (x:Type->Type) (y:Type->Type) = injI_ x y (Mk x)
*)

// P in SMT logic -- accepted but hard to use for the rest of the proof
//                   (the SMT solver doesn't prove false_of_Pp automatically)
// type P (x:Type) = (exists (a:Type->Type). i a == x /\ ~(a x))

// P in constructive logic -- not accepted, for no good reason (filed as #350)!
noeq type cexists_type_to_type : ((Type->Type) -> Type) -> Type =
  | ExTypeToTypeIntro : #p:((Type->Type) -> Type) -> t:(Type -> Type) ->
                         h:(p t) -> cexists_type_to_type p

val exInd : #p:((Type->Type) -> Type) -> p0:Type ->
             (x:(Type->Type) -> p x -> Tot p0) -> cexists_type_to_type p -> Tot p0
let exInd (#p:((Type->Type) -> Type)) (p0:Type) 
          (f: (x:(Type->Type) -> p x -> Tot p0)) (h:cexists_type_to_type p) = 
    match h with 
       | ExTypeToTypeIntro #q #t h -> f t h


#set-options "--log_types"

(** Hitting non-cumulativity:
(Error) Expected expression of type "Type((S n'ua))";
got expression "x" of type "Type(n'ua)"
*)
type r (x:Type u#a) =
  cexists_type_to_type
    (fun (a:Type u#a -> Type0) -> cand (ceq_type (i a) x) (cnot (a x)))


val aux : h:r p ->
                 a:(Type->Type) ->
                 h12:(cand (ceq_type (i a) p) (cnot (a p))) ->
                   Tot cfalse
let aux h (a:(Type->Type)) h12 =
  let Conj h1 h2 = h12 in
  injI a r; // h2 h -- this should finish the proof but causes bogus error
            // Subtyping check failed;
            // expected type (a (i (fun x -> (cexists_type_to_type
            // (fun a -> (cand (ceq_type (i a) x) ((a x) -> Tot cfalse)))))));
            // got type (r p)
  assert(a == r);
//  let h2' : cnot (a p) = magic() in h2' h -- this does not work,
//    F* doesn't seem to replace equals by equals in types (filed as #351)
    let h2' : cnot (r p) = magic() in h2' h // this does work

val false_of_rp : r p -> Tot cfalse
let false_of_rp h =
    // Using the match directly does not seem to work
    // match h with
    //     | ExTypeToTypeIntro 'p 'a h -> aux h 'a h
  exInd // #(fun (a:Type->Type) -> cand (ceq_type (i a) p) (cnot (a p)))
        cfalse
        (fun (a:(Type->Type)) -> aux h a) // needed an eta expansion
        h

val have_rp : unit -> Tot (r p)
let have_rp () = ExTypeToTypeIntro r (Conj ReflType false_of_rp)

val contradiction : unit -> Tot cfalse
let contradiction () = false_of_rp (have_rp ())
