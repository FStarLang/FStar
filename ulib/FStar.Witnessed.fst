module FStar.Witnessed

(* An axiomatisation of the witnessed modality for preorder-indexed state monads *)

open FStar.Preorder

(* The witnessed modality *)

abstract let witnessed (#s:Type) (#rel:preorder s) (p:predicate s) 
  = stable p rel //internal representation, guarantees that all assumed witnessed predicates are stable

(* Every witnessed predicate is stable *)

val lemma_witnessed_stable: #s:Type
                         -> #rel:preorder s
                         -> p:predicate s
                         -> Lemma (requires (witnessed #s #rel p))
                                  (ensures  (stable p rel))
let lemma_witnessed_stable #s #rel p = ()

(* The functoriality (introduction) and elimination rules for the witnessed modality *)

val ax_fun: #s:Type 
         -> #rel:preorder s
         -> p:predicate s{stable p rel} 
         -> q:predicate s{stable q rel}
         -> Lemma (requires (forall x . p x ==> q x))
                  (ensures  (witnessed #s #rel p ==> witnessed #s #rel q))
let ax_fun #s #rel p q = ()

val ax_elim: #s:Type
          -> #rel:preorder s
          -> p:predicate s
          -> q:predicate s
          -> x:s
          -> Lemma (requires ((witnessed #s #rel p ==> witnessed #s #rel q) /\ p x))
                   (ensures  (q x))
let ax_elim #s #rel p q x = admit () //not provable with the current representation of witnessed

(* Rules for the interaction of the witnessed modality with other logical connectives *)

(* These would be part of the deduction system in a dedicated logic for the logic with *)
(* the witnessed modality. Here they are either proved or assumed as lemmas in F*.     *)

val ax_true: #s:Type
          -> #rel:preorder s
          -> Lemma (witnessed #s #rel (fun _ -> True))
let ax_true #s #rel = ()

val ax_false: #s:Type
           -> #rel:preorder s
           -> Lemma (requires (witnessed #s #rel (fun _ -> False)))
                    (ensures  (False))
let ax_false #s #rel = admit () //not provable with the current representation of witnessed

val ax_and: #s:Type
         -> #rel:preorder s
         -> p:predicate s
         -> q:predicate s
         -> Lemma (requires (witnessed #s #rel p /\ witnessed #s #rel q))
                  (ensures  (witnessed #s #rel (fun x -> p x /\ q x)))
let ax_and #s #rel p q = ()

val ax_or: #s:Type
        -> #rel:preorder s
        -> p:predicate s{stable p rel}
        -> q:predicate s{stable p rel}
        -> Lemma (requires (witnessed #s #rel (fun x -> p x \/ q x)))
                 (ensures  (witnessed #s #rel p \/ witnessed #s #rel q))
let ax_or #s #rel p q = ()                  

val ax_impl: #s:Type
          -> #rel:preorder s
          -> p:predicate s{stable p rel}
          -> q:predicate s{stable q rel}
          -> Lemma (requires ((witnessed #s #rel p ==> witnessed #s #rel q) /\ stable (fun x -> p x ==> q x) rel))
                   (ensures  (witnessed #s #rel (fun x -> p x ==> q x)))
let ax_impl #s #rel p q = ()

val ax_forall: #s:Type
            -> #rel:preorder s
            -> p:predicate (s * s)
            -> Lemma (requires (forall x . witnessed #s #rel (fun y -> p (x,y))))
                     (ensures  (witnessed #s #rel (fun y -> forall x . p (x,y))))
let ax_forall #s #rel p = admit () //not provable with the current representation of witnessed

val ax_exists: #s:Type
            -> #rel:preorder s
            -> p:predicate (s * s)
            -> Lemma (requires (witnessed #s #rel (fun x -> exists y . p (x,y))))
                     (ensures  (exists y . (witnessed #s #rel (fun x -> p (x,y)))))
let ax_exists #s #rel p = admit () //not provable with the current representation of witnessed

(* Using the axioms above, the witnessed modality in fact commutes with other logical connectives. *)

val lemma_true: #s:Type
             -> #rel:preorder s
             -> Lemma (witnessed #s #rel (fun _ -> True) <==> True)
let lemma_true #s #rel = ()

val lemma_false: #s:Type
              -> #rel:preorder s
              -> Lemma (witnessed #s #rel (fun _ -> False) <==> False)
let lemma_false #s #rel = ax_false #s #rel

val lemma_and: #s:Type
            -> #rel:preorder s
            -> p:predicate s
            -> q:predicate s
            -> Lemma (requires (stable p rel /\ stable q rel))
                     (ensures  ((witnessed #s #rel p /\ witnessed #s #rel q) 
                                <==> 
                                (witnessed #s #rel (fun x -> p x /\ q x))))
let lemma_and #s #rel p q = ()

val lemma_or: #s:Type
           -> #rel:preorder s
           -> p:predicate s{stable p rel}
           -> q:predicate s{stable p rel}
           -> Lemma (requires (stable (fun x -> p x \/ q x) rel))
                    (ensures  ((witnessed #s #rel (fun x -> p x \/ q x)) 
                               <==> 
                               (witnessed #s #rel p \/ witnessed #s #rel q)))
let lemma_or #s #rel p q = ()                  

val lemma_impl: #s:Type
             -> #rel:preorder s
             -> p:predicate s{stable p rel}
             -> q:predicate s{stable q rel}
             -> Lemma (requires (stable (fun x -> p x ==> q x) rel))
                      (ensures  (((witnessed #s #rel p ==> witnessed #s #rel q)) 
                                 <==> 
                                 (witnessed #s #rel (fun x -> p x ==> q x))))
let lemma_impl #s #rel p q = ()

val lemma_forall: #s:Type
               -> #rel:preorder s
               -> p:predicate (s * s)
               -> Lemma (requires (forall x . stable (fun y -> p (x,y)) rel))
                        (ensures  ((forall x . witnessed #s #rel (fun y -> p (x,y))) 
                                   <==> 
                                   (witnessed #s #rel (fun y -> forall x . p (x,y)))))
let lemma_forall #s #rel p = ax_forall #s #rel p //not provable with the current representation of witnessed

val lemma_exists: #s:Type
               -> #rel:preorder s
               -> p:predicate (s * s)
               -> Lemma (requires (stable (fun x -> (exists y . p (x,y))) rel))
                        (ensures  ((witnessed #s #rel (fun x -> exists y . p (x,y))) 
                                   <==> 
                                   (exists y . (witnessed #s #rel (fun x -> p (x,y))))))
let lemma_exists #s #rel p = ax_exists #s #rel p

(* A useful lemma for the metatheory, allows us to introduce witnessed relative to the "current" world *)

val lemma_relative_intro: #s:Type
                       -> #rel:preorder s
                       -> p:predicate s
                       -> x:s
                       -> Lemma (requires ((witnessed #s #rel (fun y -> rel x y) ==> p x) /\ stable p rel))
                                (ensures  (witnessed #s #rel (fun y -> rel x y) ==> witnessed #s #rel p))
let lemma_relative_intro #s #rel p x = ()
