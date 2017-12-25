module FStar.Monotonic.Witnessed

open FStar.Preorder

(* 
   A module that defines the 'witnessed' logical capability/modality
   that is the basis of reasoning about monotonic state in F*, as
   discussed in Ahman et al.'s POPL 2018 paper "Recalling a Witness:
   Foundations and Applications of Monotonic State". Compared to the 
   POPL paper, where 'witnessed' and 'witnessed_weakening' were 
   simply postulated as axioms, this module defines them on top of 
   a more basic hybrid modal extension of F*'s reasoning logic (see 
   the corresponding fst file). Also, compared to the POPL paper, this 
   module proves many additional logical properties of 'witnessed'.
*)

(* Witnessed modality *)

val witnessed : #state:Type -> #rel:preorder state -> p:(state -> Type0) -> Type0

(* Weakening for the witnessed modality *)

val witnessed_weakening : #state:Type
                       -> #rel:preorder state
                       -> p:(state -> Type0)
                       -> q:(state -> Type0)
                       -> Lemma (requires (forall s . p s ==> q s))
                                (ensures  (witnessed #state #rel p ==> witnessed #state #rel q))
                          [SMTPat (witnessed #state #rel p); SMTPat (witnessed #state #rel q)]

(* Some logical properties of the witnessed modality *)

val witnessed_constant : #state:Type
                      -> #rel:preorder state
                      -> p:Type0
                      -> Lemma (witnessed #state #rel (fun _ -> p) <==> p)
                         [SMTPat (witnessed #state #rel (fun _ -> p))]

val witnessed_nested : #state:Type
                    -> #rel:preorder state
                    -> p:(state -> Type0)
                    -> Lemma (witnessed #state #rel (fun _ -> witnessed #state #rel p) <==> witnessed #state #rel p)
                       [SMTPat (witnessed #state #rel (fun _ -> witnessed #state #rel p))]

val witnessed_and_1 : #state:Type
                   -> #rel:preorder state
                   -> p:(state -> Type0) 
                   -> q:(state -> Type0)
                   -> Lemma (requires (witnessed #state #rel (fun s -> p s /\ q s)))
                            (ensures  (witnessed #state #rel p /\ witnessed #state #rel q))
                      [SMTPat (witnessed #state #rel (fun s -> p s /\ q s))]

val witnessed_and_2 : #state:Type
                   -> #rel:preorder state
                   -> p:(state -> Type0) 
                   -> q:(state -> Type0)
                   -> Lemma (requires (witnessed #state #rel p /\ witnessed #state #rel q))
                            (ensures  (witnessed #state #rel (fun s -> p s /\ q s)))
                      [SMTPat (witnessed #state #rel (fun s -> p s /\ q s))]

val witnessed_or : #state:Type
                -> #rel:preorder state
                -> p:(state -> Type0)
                -> q:(state -> Type0)
                -> Lemma (requires (witnessed #state #rel p \/ witnessed #state #rel q))
                         (ensures  (witnessed #state #rel (fun s -> p s \/ q s)))
                   [SMTPat (witnessed #state #rel (fun s -> p s \/ q s))]

val witnessed_impl : #state:Type
                  -> #rel:preorder state
                  -> p:(state -> Type0)
                  -> q:(state -> Type0)
                  -> Lemma (requires (witnessed #state #rel (fun s -> p s ==> q s) /\ witnessed #state #rel p))
                           (ensures  (witnessed #state #rel q))
                     [SMTPat (witnessed #state #rel (fun s -> p s ==> q s))]

val witnessed_forall : #state:Type
                    -> #rel:preorder state
                    -> #t:Type0
                    -> p:(state -> t -> Type0) 
                    -> Lemma (requires (witnessed #state #rel (fun s -> forall x . p s x)))
                             (ensures  (forall x . witnessed #state #rel (fun s -> p s x)))
                       [SMTPat (witnessed #state #rel (fun s -> forall x . p s x))]

val witnessed_exists : #state:Type
                    -> #rel:preorder state
                    -> #t:Type0
                    -> p:(state -> t -> Type0) 
                    -> Lemma (requires (exists x . witnessed #state #rel (fun s -> p s x)))
                             (ensures  (witnessed #state #rel (fun s -> exists x . p s x)))
                       [SMTPat (witnessed #state #rel (fun s -> exists x . p s x))]
