(*--build-config
    other-files:FStar.Constructive.fst FStar.Classical.fst
  --*)
module Berardi

open FStar.Constructive

(* Berardi's paradox:
   https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Berardi.html
   This was brought to our attention by Maxime Denes.
*)

(* Ingredient #1: impredicative polymorphism in Type *)

type t = a:Type -> Tot a
val foo : t -> Tot t
let foo f = f t

(* Ingredient #2: excluded middle in Type *)

assume val excluded_middle_constr : a:Type -> Tot (cor a (cnot a))

(* #1 + #2 imply proof/term irrelevance in Type
  (so this assume should go away) *)

assume val proof_irrelevance : #a:Type -> x:a -> y:a -> Tot (ceq x y)

val false_elim : u:unit{false} -> Tot 'a
let false_elim () = ()

(* Proof irrelevance in Type implies False *)

val contradiction : unit -> Tot cfalse
let contradiction () = false_elim (ceq_eq (proof_irrelevance true false))


(* Another place where this could happen is in the refinement logic *)

(* the SMT solver can of course prove excluded middle
   (here had to pass silly unit argument) *)
val excluded_middle_ref : p:Type -> unit -> Lemma (p \/ ~p)
let excluded_middle_ref () = ()

(* we would then need to trick the SMT solver to prove Berardi's paradox;
   given that it also has foralls it doesn't seem impossible that this might work *)

assume val proof_irrelevance_ref : #a:Type -> x:a -> y:a -> Lemma (x = y)

val contradiction_ref : unit -> Lemma false
let contradiction_ref () = proof_irrelevance_ref true false

(* Some more work on this with Maxime on Sept 3, 2015 *)

assume val get_proof: a:Type -> Ghost a (requires a) (ensures (fun _ -> True))

val excluded_middle'' : p:Type -> unit -> GTot (p \/~p)
let excluded_middle'' (p:Type) () = get_proof (p\/~p)

type pow (p:Type) = p -> Tot bool

// CH: no dependent record types? why not?
// type retract' 'a 'b = {i : ('a -> 'b); j : ('b -> 'a);
//                       inv : (a:Type -> GTot (ceq (j (i a)) a))}
// berardi.fst(63,53-63,54) : Error Identifier not found: [i] 

type retract 'a 'b = ( i : ('a -> Tot 'b) &
                       j : ('b -> Tot 'a) &
                       inv : (x:'a -> GTot (ceq (j (i x)) x)) )

val i : retract 'a 'b -> Tot ('a -> Tot 'b)
// let i r = match r with (|xi,_,_|) -> xi -- works
// let i (a:Type) (b:Type)  = MkDTuple3._1 // works
let i r = MkDTuple3._1 r // works

// let i = MkDTuple3._1 // does not work!
// berardi.fst(82,8-82,20) : Error
// Expected expression of type "((retract 'a 'b) -> 'a -> Tot 'b)";
// got expression "(_1 )" of type
// "(projectee:(DTuple3 U6418 U6419 U6420) -> Tot (a projectee))"

// berardi.fst(83,8-83,20) : Error
// Expected expression of type
// "(#'a:Type -> #'b:Type -> (retract 'a 'b) -> Tot ('a -> Tot 'b))";
// got expression "(_1 #U6419 #U6420 #U6421)" of type
// "(projectee:(DTuple3 U6419 U6420 U6421) -> Tot (a #U6419 #(fun U6419 -> (U6420 _)) #(fun x:U6419 (U6420 x) -> (U6421 x _)) projectee))"

val j : retract 'a 'b -> 'b -> Tot 'a
let j r = MkDTuple3._2 r // works

// val inv : a:Type -> b:Type -> r:retract a b ->
//   x:a -> GTot (ceq (j r (i r x)) x)
let inv (#a:Type) (#b:Type) (r:retract a b) =
  MkDTuple3._3 #(a -> Tot b)
               #(fun i -> (b -> Tot a))
               #(fun (i:a -> Tot b) 
                     (j:b -> Tot a) -> (x:a -> GTot (ceq (j (i x)) x))) r
// CH: leaking c variable!
// let inv : (a:Type -> b:Type -> r:(retract a b) -> Tot (c r (_1 r) (_2 r)))

// CH: without an annotation there are still uninstantiated arguments!
// let inv (a:Type) (b:Type) (r:retract a b) = MkDTuple3._3

// let inv : (a:Type -> b:Type -> r:(retract a b) -> Tot
//   (projectee:(DTuple3 (U6569 a b r) (U6570 a b r) (U6571 a b r)) ->
//     Tot (c projectee (_1 projectee) (_2 projectee))))

// let inv : (a:Type -> b:Type -> r:(retract a b) -> Tot
//   (projectee:(DTuple3 (U6569 a b r) (U6570 a b r) (U6571 a b r)) ->
//   Tot (c #(U6569 a b r) #(fun (U6569 a b r) -> (U6570 a b r _)) #(fun
//   x:(U6569 a b r) (U6570 a b r x) -> (U6571 a b r x _)) projectee (_1
//   #(U6569 a b r) #(fun (U6569 a b r) -> (U6570 a b r _)) #(fun
//   x:(U6569 a b r) (U6570 a b r x) -> (U6571 a b r x _)) projectee) (_2
//   #(U6569 a b r) #(fun (U6569 a b r) -> (U6570 a b r _)) #(fun
//   x:(U6569 a b r) (U6570 a b r x) -> (U6571 a b r x _)) projectee))))

type retract_cond 'a 'b = ( i2 : ('a -> Tot 'b) & j2 : ('b -> Tot 'a) &
       inv2 : (retract 'a 'b -> x:'a -> GTot (ceq (j2 (i2 x)) x)) )

val i2 : retract_cond 'a 'b -> Tot ('a -> Tot 'b)
let i2 r = MkDTuple3._1 r

val j2 : retract_cond 'a 'b -> 'b -> Tot 'a
let j2 r = MkDTuple3._2 r

let inv2 (#a:Type) (#b:Type) (r:retract_cond a b) =
  MkDTuple3._3 #(a -> Tot b)
               #(fun i -> (b -> Tot a))
               #(fun (i:a -> Tot b) (j:b -> Tot a) ->
                     (retract a b -> x:a -> GTot (ceq (j (i x)) x))) r

assume val ac : r:retract_cond 'a 'b -> retract 'a 'b -> x:'a ->
    GTot (ceq ((j2 r) (i2 r x)) x)
// let ac r = inv2 r
// berardi.fst(142,11-142,17): Subtyping check failed; expected type ((retract 'a 'b) -> x:'a -> GTot ((ceq (j2 r (i2 r x)) x))); got type (c r (_1 r) (_2 r))

assume val false_elim' : False -> Tot 'a

val l1 : a:Type -> b:Type -> GTot (retract_cond (pow a) (pow b))
let l1 (a:Type) (b:Type) =
  if FStar.Classical.excluded_middle (retract (pow a) (pow b)) then
    let p = get_proof (retract (pow a) (pow b)) in
    let (|f0, g0, e|) = p in (|f0, g0, (fun _ -> e)|)
  else
    let p:(retract (pow a) (pow b) -> Tot False) = magic() in
//        get_proof (retract (pow a) (pow b) ==> False) in -- CH: really?
//     Expected type "((retract (pow a) (pow b)) -> Tot False)";
//     got type      "((retract (pow a) (pow b)) ==> False)"
    let f0 (x:pow a) (y:b) = false in
    let g0 (x:pow b) (y:a) = false in
    let e (r:retract (pow a) (pow b)) = false_elim' (p r) in
    // let e : (retract a b -> x:a -> GTot (ceq (j2 (i2 x)) x)) = magic() in
    //  -- this doesn't work either
    (| f0, g0, magic() |)
    // CH: the magic should be e, but that gives Unknown assertion failed

// CH: can't match on l_or type
// let l1 (a:Type) (b:Type) () =
//   let x:((retract (pow a) (pow b)) \/ (~ (retract (pow a) (pow b)))) =
//     excluded_middle'' (retract (pow a) (pow b)) () in
//   match x with
//   | Left -> magic()
//   | Right -> magic()
// berardi.fst(140,2-142,20) : Error
// Expected type "((retract (pow a) (pow b)) \/ (~ (retract (pow a) (pow b))))";
// got type "(((U6898 a b _2_71 x) -> Tot (U6898 a b _2_71 x)) \/ (U6900 a b _2_71 x))"

type U = p:Type -> Tot (pow p)

val f : U -> Tot (pow U)
let f u = u U

assume val g : pow U -> GTot U
// let g (h:pow U) = fun (x:Type) ->
//   let lX = j2 (l1 x U) in
//   let rU = i2 (l1 U U) in
//   lX (rU h)
// berardi.fst(173,0-176,11) : Error
// Expected a term of type "((pow U) -> GTot (U))";
// got a function "(fun h x -> let  lX:<UNKNOWN> = (j2 (l1 x U)) in let  rU:<UNKNOWN> = (i2 (l1 U U)) in (lX (rU h)))" (Curried function, but not total)

// val r : GTot U
// Kinds "Effect" and "Type" are incompatible
// CH: should be able to define the effect of top level computations?
// CH: need to pass a silly unit
val r : unit -> GTot U
let r () = g (fun (u:U) -> op_Negation (u U u))

assume val not_has_fixpoint : unit -> Tot (ceq ((r()) U (r()))
                                                (op_Negation ((r()) U (r()))))
// let not_has_fixpoint () = Eq bool (r U r)

val contradict : unit -> Lemma false
let contradict () = ignore (not_has_fixpoint ())
