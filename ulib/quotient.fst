module Quotient

open FStar.Tactics

open FStar.FunctionalExtensionality
module SEM = FStar.StrongExcludedMiddle
module C = FStar.Classical
module S = FStar.Squash

type rel (a:Type) = a -> a -> Type

let equivalence_relation (#a:Type) (r:rel a) =
  (forall x. r x x) /\ (forall x y. r x y ==> r y x) /\ (forall x y z. r x y /\ r y z ==> r x z)

let equiv (a:Type) = r:rel a{equivalence_relation r}

let equivalence_class (#a:Type) (p: a -> GTot bool) (r:equiv a) =
  exists x. p x /\ (forall y. r x y <==> p y)

let quotient (a:Type u#a) (r:equiv a): Type u#a = p:(a -> GTot bool){equivalence_class p r}

let prop = a:Type{forall (x y: a). x == y}

let squash (#a:Type) (r:equiv a) (x:a) : p:(quotient a r) =
  let f (y:a) : GTot bool = SEM.strong_excluded_middle (r x y) in
  f

let forall_to_exists_lem (#a #c: Type) (#b:a -> Type) (f : (x:a) -> Prims.squash (b x ==> c))
  : Prims.squash ((exists x. b x) ==> c)
= let h (x:a) : Lemma (b x ==> c) = f x in
  C.forall_to_exists h ;
  S.get_proof ((exists x. b x) ==> c)

let destruct_exists_arg : tactic (binder * binder) =
  let fail () = fail "not of the form (exists x. a) ==> b" in
  g <-- cur_goal ;
  match term_as_formula g with
  | Implies t _ ->
    // if not (Exists? (term_as_formula t))
    // then fail ()
    // else
    begin
      apply (quote_lid ["Quotient" ; "forall_to_exists_lem"]) ;;
      x <-- intro ;
      h <-- implies_intro ;
      return (x, h)
    end
  | _ -> fail ()

let tau : tactic unit =
  hx <-- forall_intros ;
  dump "A" ;;
  h <-- destruct_exists_arg ;
  let (y, h1) = h in
  dump "B" ;;
  smt

let intro_quotient (#a #b:Type) (ra:equiv a) (rb:equiv b) (f: a -> quotient b rb)
  : Pure (quotient a ra -> quotient b rb)
    (requires (forall x y. ra x y ==> f x == f y))
    (ensures (fun g -> forall x. g (squash ra x) == f x))
=
  let g (p:quotient a ra) : quotient b rb =
    let h = fun (y:b) -> SEM.strong_excluded_middle (exists x. p x /\ f x y) in
    assert_by_tactic
      (norm [Delta] ;; h1 <-- destruct_exists_arg ; smt)
      (equivalence_class p ra ==> equivalence_class h rb) ;
    h
  in
  assert (forall x y. g (squash ra x) y == f x y) ;
  assert (forall x. g (squash ra x) `gfeq` f x) ;
  g

let op_String_Access (#a:Type) (x:a) (r:equiv a) = squash r x

let finest_equiv (#a:Type) : equiv a = let h = fun x y -> x == y in h

let squash_finest_inj_lemma (a:Type) (x y:a)
  : Lemma (requires (x.[finest_equiv] == y.[finest_equiv]))
    (ensures (x == y))
= ()

let quotient_extensionality (#a:Type) (ra:equiv a) (p1 p2:quotient a ra)
  : Lemma (requires (exists x. p1 x /\ p2 x)) (ensures (p1 == p2))
= assert (forall x. p1 x == p2 x) ;
  assert (p1 `gfeq` p2)

let squash_extensionality (#a:Type) (r:equiv a) (p:quotient a r) (x:a)
  : Lemma (requires (p x)) (ensures (p == x.[r]))
= assert (p x /\ x.[r] x) ;
  quotient_extensionality r p x.[r]

let squash_extensionality' (#a:Type) (r:equiv a) (p:quotient a r)
  : Lemma (forall x. p x ==> p == x.[r])
= C.forall_intro (C.move_requires (squash_extensionality #a r p))

let squash_finest_surj_lemma (a:Type) (p:quotient a finest_equiv)
  : Lemma (exists x. p == x.[finest_equiv]) =
  assert (exists x. p x) ;
  squash_extensionality' #a finest_equiv p


let projector (a:Type) = f:(a -> a){forall x. f x == f (f x)}

let pquotient (a:Type) (f:projector a) = x:a{x == f x}

let psquash (#a:Type) (f:projector a) (x:a) : pquotient a f = f x

let pequiv (#a:Type) (f:projector a) : equiv a =
  let r x y = f x == f y in
  r

let pquotient_to_quotient (#a:Type) (f:projector a) : pquotient a f -> quotient a (pequiv f) =
  let h (x:pquotient a f) = x.[pequiv f] in
  h

let pquotient_to_quotient_inj (#a:Type) (f:projector a) :
    Lemma (forall (x y:pquotient a f). pquotient_to_quotient f x == pquotient_to_quotient f y ==> x == y)
= ()

let pquotient_to_quotient_surj (#a:Type) (f:projector a) (y:quotient a (pequiv f)) :
    Lemma (exists x. y == pquotient_to_quotient f x)
= assert (forall x. y x ==> y (f x)) ;
  assert (exists (x:pquotient a f). y x) ;
  squash_extensionality' #a (pequiv f) y

(* let pquotient_intro (#a #b:Type) (f:projector a) (h:a -> b) *)
(*   : Pure (pquotient a f) *)
(*     (requires (forall x. h x = h (f x))) *)
(*     (ensures (fun g -> g (psquash x))) *)


let prop_equiv (a b:prop) :Lemma (requires (a == b)) (ensures (a <==> b)) = ()

(* let _ = assert_by_tactic (h <-- forall_intros ; dump "A" ;; smt) (forall (x:nat) (y:int{y < 0}). x =!= y) *)

let intro_quotient_type (#a:Type) (r:equiv a) (f: a -> prop)
  : Ghost (quotient a r -> prop)
    (requires (forall x y. r x y ==> f x == f y))
    (ensures (fun g -> forall x. g (squash r x) <==> f x))
= let g (p:quotient a r) : prop = exists (x:a). p x /\ f x in
  assert (forall x. f x ==> (exists x'. squash r x x' /\ f x')) ;
  assert (forall x. f x ==> g (squash r x)) ;
  assert (forall x p. p == squash r x ==> g p == (exists x'. p x' /\ f x')) ;
  let h (x:a) (p:quotient a r) : Lemma (requires (p == squash r x)) (ensures (g p ==> f x)) =
      assert (g p == (exists x'. p x' /\ f x'));
      prop_equiv (g p) (exists x'. p x' /\ f x') ;
      assert ((exists x'. p x' /\ f x') ==> f x)
  in
  let h1 (x:a) : Lemma (let p = squash r x in g p ==> f x) = h x (squash r x) in
  C.forall_intro h1 ;
  assert (forall x. g (squash r x) ==> f x) ;
  (* assert_by_tactic *)
  (*   ( x <-- forall_intro ; *)
  (*     exact (apply (quote h1) x) *)
  (*   ) *)
  (*   (forall x.let p = squash r x in g p ==> f x) *)
  g


let imod5 :  rel int = fun x y -> b2t (x = y % 5)
let mod5 : equiv int = admit () ; imod5

let test = (2).[mod5] = (7).[mod5]
