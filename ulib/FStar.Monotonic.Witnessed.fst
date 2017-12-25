module FStar.Monotonic.Witnessed

open FStar.Preorder

(* NOT EXPOSED BY THE INTERFACE [start] *)

(* 
   A hybrid modal extension to F*'s classical reasoning logic:
     - extends F*'s logic with two hybrid modal operators (get, set)
     - extends F*'s logic with corresponding logical axioms, based
       on the Kripke semantics of these two hybrid modal operators:

         w |= get p   iff   w |= p w

         w |= set p w'   iff   w' |= p

    We do not expose these modal operators to the users directly.
    Instead we use them below to define the 'witnessed' modality 
    which is the basis of reasoning about monotonic state in F*, 
    as discussed in Ahman et al.'s POPL 2018 paper "Recalling a 
    Witness: Foundations and Applications of Monotonic State".
*)

(* Hybrid modal operators *)
assume type get : #world:Type -> (world -> Type0) -> Type0
assume type set : #world:Type -> Type0 -> world -> Type0

(* Weakening for the get operator *)
assume val get_weakening : #world:Type
                        -> p:(world -> Type0)
                        -> q:(world -> Type0)
                        -> Lemma (requires (forall w . p w ==> q w))
                                 (ensures  (get p ==> get q))
                           [SMTPat (get p); SMTPat (get q)]

(* Interaction axioms between the get and set operators *)
assume val get_set_axiom : #world:Type
                        -> p:Type0
                        -> Lemma (get #world (set p) <==> p)
                           [SMTPat (get #world (set p))]

assume val set_get_axiom : #world:Type
                        -> w:world
                        -> p:(world -> Type0)
                        -> Lemma (set (get p) w <==> set (p w) w)
                           [SMTPat (set (get p) w)]

assume val set_set_axiom : #world:Type
                        -> w:world
                        -> w':world
                        -> p:Type0
                        -> Lemma (set (set p w') w <==> set p w')
                           [SMTPat (set (set p w') w)]

(* Useful derivable get lemma *)

val get_constant_lemma : #world:Type
                      -> p:Type0
                      -> Lemma (get #world (fun _ -> p) <==> p)
                         [SMTPat (get #world (fun _ -> p))]
let get_constant_lemma #world p = get_set_axiom #world p

(* Get and set commute with (non-modal) logical connectives *)

val get_true : #world:Type
            -> Lemma (get #world (fun _ -> True))
               [SMTPat (get #world (fun _ -> True))]
let get_true #world = ()

assume val set_true : #world:Type
                   -> w:world
                   -> Lemma (set True w)
                      [SMTPat (set True w)]

val get_false : #world:Type
             -> Lemma (requires (get #world (fun _ -> False)))
                      (ensures  (False))
                [SMTPat (get #world (fun _ -> False))]
let get_false #world = ()

assume val set_false : #world:Type
                    -> w:world
                    -> Lemma (requires (set False w)) 
                             (ensures  (False))
                       [SMTPat (set False w)]

val get_and_1 : #world:Type
             -> p:(world -> Type0)
             -> q:(world -> Type0)
             -> Lemma (requires (get (fun w -> p w /\ q w)))
                      (ensures  (get p /\ get q))
                [SMTPat (get (fun w -> p w /\ q w))]
let get_and_1 #world p q = ()

assume val set_and_1 : #world:Type
                    -> w:world    
                    -> p:Type0
                    -> q:Type0
                    -> Lemma (requires (set (p /\ q) w))
                             (ensures  (set p w /\ set q w))
                       [SMTPat (set (p /\ q) w)]

assume val get_and_2 : #world:Type
                    -> p:(world -> Type0)
                    -> q:(world -> Type0)
                    -> Lemma (requires (get p /\ get q))
                             (ensures  (get (fun w -> p w /\ q w)))
                       [SMTPat (get (fun w -> p w /\ q w))]

assume val set_and_2 : #world:Type
                    -> w:world
                    -> p:Type0
                    -> q:Type0
                    -> Lemma (requires (set p w /\ set q w))
                             (ensures  (set (p /\ q) w))
                       [SMTPat (set (p /\ q) w)]

val get_or_1 : #world:Type
            -> p:(world -> Type0)
            -> q:(world -> Type0)
            -> Lemma (requires (get p \/ get q))
                     (ensures  (get (fun w -> p w \/ q w)))
               [SMTPat (get (fun w -> p w \/ q w))]
let get_or_1 #world p q = ()

assume val set_or_1 : #world:Type
                   -> w:world
                   -> p:Type0
                   -> q:Type0
                   -> Lemma (requires (set p w \/ set q w))
                            (ensures  (set (p \/ q) w))
                      [SMTPat (set (p \/ q) w)]

assume val get_or_2 : #world:Type
                   -> p:(world -> Type0)
                   -> q:(world -> Type0)
                   -> Lemma (requires (get (fun w -> p w \/ q w)))
                            (ensures  (get p \/ get q))
                      [SMTPat (get (fun w -> p w \/ q w))]

assume val set_or_2 : #world:Type
                   -> w:world
                   -> p:Type0
                   -> q:Type0
                   -> Lemma (requires (set (p \/ q) w))
                            (ensures  (set p w \/ set q w))
                      [SMTPat (set (p \/ q) w)]

val get_impl_1 : #world:Type
              -> p:(world -> Type0)
              -> q:(world -> Type0)
              -> Lemma (requires (get (fun w -> p w ==> q w) /\ get p))
                       (ensures  (get q))
                 [SMTPat (get (fun w -> p w ==> q w))]
let get_impl_1 #world p q = 
  get_and_2 (fun w -> p w ==> q w) p; 
  get_weakening (fun w -> (p w ==> q w) /\ p w) q

assume val set_impl_1 : #world:Type
                     -> w:world
                     -> p:Type0
                     -> q:Type0
                     -> Lemma (requires (set (p ==> q) w /\ set p w))
                              (ensures  (set q w))
                        [SMTPat (set (p ==> q) w)]

assume val get_impl_2 : #world:Type
                     -> p:(world -> Type0)
                     -> q:(world -> Type0)
                     -> Lemma (requires (get p ==> get q))
                              (ensures  (get (fun w -> p w ==> q w)))
                        [SMTPat (get (fun w -> p w ==> q w))]

assume val set_impl_2 : #world:Type
                     -> w:world
                     -> p:Type0
                     -> q:Type0
                     -> Lemma (requires (set p w ==> set q w))
                              (ensures  (set (p ==> q) w))
                        [SMTPat (set (p ==> q) w)]

val get_forall_1_aux : #world:Type
                    -> #t:Type
                    -> p:(world -> t -> Type0)
                    -> x:t
                    -> Lemma (requires (get (fun w -> forall x . p w x)))
                             (ensures  (get (fun w -> p w x)))
                       [SMTPat (get (fun w -> p w x)); SMTPat (get (fun w -> forall (x:t) . p w x))]
let get_forall_1_aux #world #t p x = 
  get_weakening (fun w -> forall x . p w x) (fun w -> p w x)

val get_forall_1 : #world:Type
                -> #t:Type
                -> p:(world -> t -> Type0)
                -> Lemma (requires (get (fun w -> forall x . p w x)))
                         (ensures  (forall x . get (fun w -> p w x)))
                   [SMTPat (get (fun w -> forall (x:t) . p w x))]
let get_forall_1 #world #t p = ()

assume val set_forall_1 : #world:Type
                       -> #t:Type
                       -> w:world
                       -> p:(t -> Type0)
                       -> Lemma (requires (set (forall x . p x) w))
                                (ensures  (forall x . set (p x) w))
                          [SMTPat (set (forall x . p x) w)]

assume val get_forall_2 : #world:Type
                       -> #t:Type
                       -> p:(world -> t -> Type0)
                       -> Lemma (requires (forall x . get (fun w -> p w x)))
                                (ensures  (get (fun w -> forall x . p w x)))
                          [SMTPat (get (fun w -> forall x . p w x))]

assume val set_forall_2 : #world:Type
                       -> #t:Type
                       -> w:world 
                       -> p:(t -> Type0)
                       -> Lemma (requires (forall x . set (p x) w))
                                (ensures  (set (forall x . p x) w))
                          [SMTPat (set (forall x . p x) w)]

val get_exists_1_aux : #world:Type
                    -> #t:Type
                    -> p:(world -> t -> Type0)
                    -> x:t
                    -> Lemma (requires (get (fun w -> p w x)))
                             (ensures  (get (fun w -> exists x . p w x)))
                       [SMTPat (get (fun w -> p w x)); SMTPat (get (fun w -> exists x . p w x))]
let get_exists_1_aux #world #t p x = 
  get_weakening (fun w -> p w x) (fun w -> exists x . p w x)

val get_exists_1 : #world:Type
                -> #t:Type
                -> p:(world -> t -> Type0)
                -> Lemma (requires (exists x . get (fun w -> p w x)))
                         (ensures  (get (fun w -> exists x . p w x)))
                   [SMTPat (get (fun w -> exists x . p w x))]
let get_exists_1 #world #t p = ()

assume val set_exists_1 : #world:Type
                       -> #t:Type
                       -> w:world
                       -> p:(t -> Type0)
                       -> Lemma (requires (exists x . set (p x) w)) 
                                (ensures  (set (exists x . p x) w))
                          [SMTPat (set (exists x . p x) w)]

assume val get_exists_2 : #world:Type
                       -> #t:Type
                       -> p:(world -> t -> Type0)
                       -> Lemma (requires (get (fun w -> exists x . p w x)))
                                (ensures  (exists x . get (fun w -> p w x)))
                          [SMTPat (get (fun w -> exists x . p w x))]

assume val set_exists_2 : #world:Type
                       -> #t:Type
                       -> w:world
                       -> p:(t -> Type0)
                       -> Lemma (requires (set (exists x . p x) w)) 
                                (ensures  (exists x . set (p x) w))
                          [SMTPat (set (exists x . p x) w)]

val get_eq : #world:Type
          -> #t:Type
          -> v:t
          -> v':t
          -> Lemma (get #world (fun _ -> v == v') <==> v == v')
             [SMTPat (get #world (fun _ -> v == v'))]
let get_eq #world #t v v' = 
  get_constant_lemma #world (v == v')

assume val set_eq : #world:Type
                 -> #t:Type
                 -> w:world
                 -> v:t
                 -> v':t
                 -> Lemma (set (v == v') w <==> v == v')
                    [SMTPat (set (v == v') w)]

(* NOT EXPOSED BY THE INTERFACE [end] *)


(* EXPOSED BY THE INTERFACE [start] *)

(* Witnessed modality *)

let witnessed (#state:Type) (#rel:preorder state) (p:(state -> Type0)) = 
  get (fun s -> forall s' . rel s s' ==> p s')

(* Weakening for the witnessed modality *)

let witnessed_weakening #state #rel p q = ()

(* Some logical properties of the witnessed modality *)

let witnessed_constant #state #rel p = 
  get_constant_lemma #state p

let witnessed_nested #state #rel p = ()

let witnessed_and_1 #state #rel p q = ()

let witnessed_and_2 #state #rel p q = 
  get_and_2 (fun s -> forall s' . rel s s' ==> p s') (fun s -> forall s' . rel s s' ==> q s')

let witnessed_or #state #rel p q = ()

let witnessed_impl #state #rel p q = 
  get_and_2 (fun s -> forall s' . rel s s' ==> p s' ==> q s') (fun s -> forall s' . rel s s' ==> p s')

let witnessed_forall #state #rel #t p = ()

let witnessed_exists #state #rel #t p = ()

(* EXPOSED BY THE INTERFACE [end] *)
