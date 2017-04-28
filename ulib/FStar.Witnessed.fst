module FStar.Witnessed

(* Natural deduction for the witnessed modality for preorder-indexed state monads *)

open FStar.Preorder

(* The witnessed modality *)

assume type witnessed: #s:Type -> rel:preorder s -> p:predicate s -> Type0

(* Syntactic sugar for "current" state/world. *)

let is_current_state_wrt (#s:Type) (x:s) (rel:preorder s) = witnessed rel (rel x) 

(* Introduction rule for the witnessed modality*)

assume val witnessed_intro: #s:Type
                         -> #rel:preorder s
                         -> x:s
                         -> p:predicate s
                         -> Lemma (requires (   x `is_current_state_wrt` rel 
                                             /\ p x 
                                             /\ stable p rel))
                                  (ensures  (witnessed rel p))
                                  [SMTPat (x `is_current_state_wrt` rel); 
                                   SMTPat (p x); 
                                   SMTPat (stable p rel)]

(* Elimination rule for the witnessed modality *)

assume val witnessed_elim: #s:Type
                        -> #rel:preorder s
                        -> x:s
                        -> x':s
                        -> p:predicate s
                        -> Lemma (requires (   x `is_current_state_wrt` rel 
                                            /\ witnessed rel p 
                                            /\ rel x x'))
                                 (ensures  (p x'))
                                 [SMTPat (witnessed rel (rel x)); 
                                  SMTPat (witnessed rel p); 
                                  SMTPat (rel x x')]

(* 
   Note that both the intro. and elm. rule are stated relative to the 
   "current" state/world x. We use the witnessed modality itself to 
   impose these preconditions. These preconditions will be additionally 
   assumed WPs of the monotonic state operations. 
*)


(* All the lemmas below are proved relative to the "current" state/world x. *)

(* The witnessed modality is functorial. *)

let witnessed_functoriality (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ (forall y . p y ==> q y)
                     /\ stable p rel
                     /\ stable q rel))
          (ensures  (witnessed rel p ==> witnessed rel q))
  = ()

(* Showing how witnessed interacts with other logical connectives. *)

let witnessed_true (#s:Type) (#rel:preorder s) (x:s) (p:predicate s)
  : Lemma (requires (x `is_current_state_wrt` rel))
          (ensures  (witnessed rel (fun _ -> True)))
  = witnessed_intro #s #rel x (fun _ -> True)

let witnessed_false (#s:Type) (#rel:preorder s) (x:s) (p:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel 
                     /\ witnessed rel (fun _ -> False)))
          (ensures  (False))
  = ()

let witnessed_and1 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel p
                     /\ witnessed rel q
                     /\ stable p rel
                     /\ stable q rel))
          (ensures  (witnessed rel (fun y -> p y /\ q y)))
  = witnessed_intro #s #rel x (fun y -> p y /\ q y)

let witnessed_and2 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel (fun y -> p y /\ q y)
                     /\ stable p rel
                     /\ stable q rel))
          (ensures  (witnessed rel p /\ witnessed rel q))
  = ()

let witnessed_or1 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel (fun y -> p x \/ q x)
                     /\ stable p rel
                     /\ stable q rel))
          (ensures  (witnessed rel p \/ witnessed rel q))
  = ()

let witnessed_or2 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ (witnessed rel p \/ witnessed rel q)
                     /\ stable p rel
                     /\ stable q rel))
          (ensures  (witnessed rel (fun y -> p y \/ q y)))
  = witnessed_intro #s #rel x (fun y -> p y \/ q y)

let witnessed_forall1 (#s:Type) (#rel:preorder s) (x:s) (p:predicate (s * s))
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ (forall y . witnessed rel (fun z -> p (y,z)))
                     /\ stable (fun z -> forall y . p (y,z)) rel))
          (ensures  (witnessed rel (fun z -> forall y . p (y,z))))
  = witnessed_intro #s #rel x (fun z -> forall y . p (y,z))

let witnessed_forall2_aux (#s:Type) (#rel:preorder s) (x:s) (p:predicate (s * s)) (y:s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel (fun z -> forall y . p (y,z))
                     /\ (forall y . stable (fun z -> p (y,z)) rel)))
          (ensures  (witnessed rel (fun z -> p (y,z))))
          [SMTPat (x `is_current_state_wrt` rel);
           SMTPat (witnessed rel (fun z -> forall y . p (y,z))); 
           SMTPat (stable (fun z -> p (y,z)) rel)]
  = witnessed_intro #s #rel x (fun z -> p (y,z))

let witnessed_forall2 (#s:Type) (#rel:preorder s) (x:s) (p:predicate (s * s))
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel (fun z -> forall y . p (y,z))
                     /\ (forall y . stable (fun z -> p (y,z)) rel)))
          (ensures  (forall y . witnessed rel (fun z -> p (y,z))))
  = ()

let witnessed_exists1_aux (#s:Type) (#rel:preorder s) (x:s) (p:predicate (s * s)) (y:s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ p (y,x)
                     /\ (forall y . stable (fun z -> p (y,z)) rel)))
          (ensures  (ensures  (exists y . witnessed rel (fun z -> p (y,z)))))
          [SMTPat (x `is_current_state_wrt` rel);
           SMTPat (stable (fun z -> p (y,z)) rel)]
  = witnessed_intro #s #rel x (fun z -> p (y,z))

let witnessed_exists1 (#s:Type) (#rel:preorder s) (x:s) (p:predicate (s * s))
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel (fun z -> exists y . p (y,z))
                     /\ (forall y . stable (fun z -> p (y,z)) rel)))
          (ensures  (exists y . witnessed rel (fun z -> p (y,z))))
  = witnessed_elim #s #rel x x (fun z -> exists y . p (y,z))

let witnessed_exists2 (#s:Type) (#rel:preorder s) (x:s) (p:predicate (s * s))
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ (exists y . witnessed rel (fun z -> p (y,z)))
                     /\ (stable (fun z -> exists y . p (y,z)) rel)))
          (ensures  (witnessed rel (fun z -> exists y . p (y,z))))
  = witnessed_intro #s #rel x (fun z -> exists y . p (y,z))

let witnessed_impl1 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel (fun y -> p y ==> q y)
                     /\ stable p rel
                     /\ stable q rel))
          (ensures  (witnessed rel p ==> witnessed rel q))
  = ()

let witnessed_impl2_aux1 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ (forall y . (p y /\ rel y x) ==> q y)
                     /\ stable p rel
                     /\ stable q rel
                     /\ stable (fun y -> (p y /\ rel y x) ==> q y) rel))
          (ensures  (witnessed rel (fun y -> (p y /\ rel y x) ==> q y)))
  = witnessed_intro #s #rel x (fun y -> (p y /\ rel y x) ==> q y)

let witnessed_impl2_aux2 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s) (y:s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ (witnessed rel p ==> witnessed rel q)
                     /\ stable p rel
                     /\ stable q rel
                     /\ p y
                     /\ rel y x))
          (ensures  (q y))
          [SMTPat (x `is_current_state_wrt` rel);
           SMTPat (witnessed rel p ==> witnessed rel q);
           SMTPat (p y);
           SMTPat (rel y x)]
  = witnessed_intro #s #rel x (rel y);
    witnessed_intro #s #rel y p;
    witnessed_elim #s #rel y y q

let witnessed_impl2 (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ (witnessed rel p ==> witnessed rel q)
                     /\ stable p rel
                     /\ stable q rel
                     /\ stable (fun y -> (p y /\ rel y x) ==> q y) rel))
          (ensures  (witnessed rel (fun y -> (p y /\ rel y x) ==> q y)))
  = assert (witnessed rel p ==> witnessed rel q); //used to trigger witnessed_impl2_aux2
    witnessed_impl2_aux1 #s #rel x p q


(* 
   A lemma showing a suspicious behaviour of this exiomatisation of witnessed.

   When we use (witnessed rel (rel x)) to make an assumption that x is our "current" 
   state/world, then we can prove the predicate p for all past worlds of x, which 
   surely should not be the case!?! 
*)

let suspicious_lemma (#s:Type) (#rel:preorder s) (x:s) (p:predicate s) (q:predicate s) (y:s)
  : Lemma (requires (   x `is_current_state_wrt` rel
                     /\ witnessed rel p
                     /\ stable p rel
                     /\ rel y x))
          (ensures  (p y))
  = witnessed_intro #s #rel x (rel y)
