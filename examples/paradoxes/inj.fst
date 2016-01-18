(*--build-config
  options:--__temp_no_proj InjectiveTypeFormers;
  other-files: FStar.Constructive.fst
  --*)
module InjectiveTypeFormers
// We need the --__temp_no_proj flag to workaround an F* bug related to generating code for projectors

// F* unfortunately still includes injective type formers;
// these are known to be inconsistent;
// ported inconsistency proof from Lean:
// https://gist.github.com/leodemoura/0c88341bb585bf9a72e6
open FStar.Constructive

(* this file relies on a violation of the cardinality constraints of Type*)
#set-options "--cardinality warn"

type I : (Type -> Type) -> Type =
| Mk : f:(Type->Type) -> I f

val injI : x:(Type->Type) -> y:(Type->Type) ->
           Lemma (requires (I x == I y)) (ensures (x == y))
let injI (x:Type->Type) (y:Type->Type) = ()

// P in SMT logic -- accepted but hard to use for the rest of the proof
//                   (the SMT solver doesn't prove false_of_Pp automatically)
// type P (x:Type) = (exists (a:Type->Type). I a == x /\ ~(a x))

// P in constructive logic -- not accepted, for no good reason (filed as #350)!
type cexists_type_to_type : ((Type->Type) -> Type) -> Type =
  | ExTypeToTypeIntro : #p:((Type->Type) -> Type) -> t:(Type -> Type) ->
                         h:(p t) -> cexists_type_to_type p

opaque val exInd : #p:((Type->Type) -> Type) -> p0:Type ->
             (x:(Type->Type) -> p x -> Tot p0) -> cexists_type_to_type p -> Tot p0
let exInd (#p:((Type->Type) -> Type)) (p0:Type) 
          (f: (x:(Type->Type) -> p x -> Tot p0)) (h:cexists_type_to_type p) = 
    match h with 
       | ExTypeToTypeIntro 'q 't h -> f 't h

type P (x:Type) = (cexists_type_to_type (fun (a:Type->Type) ->
                     cand (ceq_type (I a) x) (cnot (a x))))

type p = I P

opaque val aux : h:P p ->
                 a:(Type->Type) ->
                 h12:(cand (ceq_type (I a) p) (cnot (a p))) ->
                   Tot cfalse
let aux h (a:(Type->Type)) h12 =
  let Conj h1 h2 = h12 in
  injI a P; // h2 h -- this should finish the proof but causes bogus error
            // Subtyping check failed;
            // expected type (a (I (fun x -> (cexists_type_to_type
            // (fun a -> (cand (ceq_type (I a) x) ((a x) -> Tot cfalse)))))));
            // got type (P p)
  assert(a == P);
//  let h2' : cnot (a p) = magic() in h2' h -- this does not work,
//    F* doesn't seem to replace equals by equals in types (filed as #351)
    let h2' : cnot (P p) = magic() in h2' h // this does work

opaque val false_of_Pp : P p -> Tot cfalse
let false_of_Pp h =
    // Using the match directly does not seem to work
    // match h with
    //     | ExTypeToTypeIntro 'p 'a h -> aux h 'a h
  exInd // #(fun (a:Type->Type) -> cand (ceq_type (I a) p) (cnot (a p)))
        cfalse
        (fun (a:(Type->Type)) -> aux h a) // needed an eta expansion
        h

opaque val have_Pp : unit -> Tot (P p)
let have_Pp () = ExTypeToTypeIntro P (Conj ReflType false_of_Pp)

opaque val contradiction : unit -> Tot cfalse
let contradiction () = false_of_Pp (have_Pp ())
