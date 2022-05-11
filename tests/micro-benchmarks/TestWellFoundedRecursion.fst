module TestWellFoundedRecursion

noeq
type ord =
  | Z : ord
  | Succ : ord -> ord
  | Lim : (nat -> ord) -> ord

let rec sum (x:ord) (y:ord) =
  match x with
  | Z -> y
  | Succ x -> Succ (sum x y)
  | Lim f -> Lim (fun n -> sum (f n) y)

noeq
type t =
  | T0 : bool -> t
  | T : (nat -> s) -> t
and s =
  | S0 : bool -> s
  | S : (nat -> t) -> s

let rec neg_t (x:t) =
  match x with
  | T0 b -> T0 (not b)
  | T f -> T (fun y -> neg_s (f y))

and neg_s (x:s) =
  match x with
  | S0 b -> S0 (not b)
  | S f -> S (fun y -> neg_t (f y))


noeq
type tree a =
  | Leaf : data:a -> tree a
  | Node : children:(nat -> tree a) -> tree a

let rec map #a #b (f:a -> b) (x:tree a)
  : Tot (tree b)
  = match x with
    | Leaf data -> Leaf (f data)
    | Node ch -> Node (fun n -> map f (ch n))

let codomain_ordering (#a:Type) (x:tree a{Node? x})
  : Lemma (forall n. Node?.children x n << x)
  = ()

let test (#a:Type) (g:nat -> tree a) (n:nat)
  : Lemma (g n << Node g)
  = //`g n << Node g` is not automatically provable in the SMT encoding
    //due to the way the triggers are set up
    //But, with a call to the lemma above, it is provable
    codomain_ordering (Node g)

//An unusual style
let rec map_alt (#a:Type0) (#b:Type0) (f:a -> b) (x:tree a)
  : Tot (tree b)
        (decreases %[x;1])
  = match x with
    | Leaf data -> Leaf (f data)
    | Node ch -> Node (map_alt' #a #b f ch)
and map_alt' (#a:Type0) (#b:Type0) (f:a -> b) (g: (nat -> tree a))
  : Tot (nat -> tree b)
        (decreases %[Node g; 0])
  = fun n -> codomain_ordering (Node g);  //sadly, seems to require a call to the lemma
          map_alt f (g n)


noeq
type stream' (a:Type) =
  | SNil': stream' a
  | SCons': a & (unit -> stream' a) -> stream' a

//we do not generate well-foundedness axioms for function within
//other inductives, i.e., we don't destruct the pair above
[@@expect_failure [19]]
let rec fmap_stream' (#a #b:Type) (f:a -> b) (x:stream' a) : stream' b =
  match x with
  | SNil' -> SNil'
  | SCons' (h, t) ->
    let ft () = fmap_stream' f (t ()) in
    SCons' (f h, ft)

//You have to write it this way
noeq
type stream (a:Type) =
  | SNil: stream a
  | SCons: _:a -> f:(unit -> stream a) -> stream a

let rec fmap_stream (#a #b:Type) (f:a -> b) (x:stream a) : stream b =
  match x with
  | SNil -> SNil
  | SCons h t ->
    let ft () = fmap_stream f (t ()) in
    SCons (f h) ft

noeq
type test1 (a:Type) =
  | Test1: f:(nat -> a) -> test1 a

noeq
type test2 (a:Type) =
  | Test2: g:test1 (test2 a) -> test2 a

let wf_test1 (#a:_) (x:test1 a) (y:nat)
  : Lemma (Test1?.f x y << x)
  = ()

let rec map_test2 (#a #b:Type) (t:test2 a) (f: a -> b) : test2 b =
    let Test2 (Test1 g) = t in
    Test2 (Test1 (fun (x:nat) -> wf_test1 (Test1 g) x; map_test2 #a #b (g x) f))

//////////////////////////////////////////////////////////////////////////////////////////
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
noeq
type tf =
  | TF: f:(nat ^-> tf) -> tf

let rec test_tf (f:tf) =
    match f with
    | TF g -> TF (on_dom nat (fun x -> test_tf (g x)))


//////////////////////////////////////////////////////////////////////////////////////////

//// Termination checking using accessibility predicates ////

//////////////////////////////////////////////////////////////////////////////////////////

//We can write the ackermann function (and prove its termination) this way:

let rec ackermann (m n:nat) : Tot nat (decreases %[m; n]) =
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

//The proof above relies on the in-built lexicographic ordering in F*
//F* also provides termination checking based on accessibility predicates
//  using which we can build our own lexicographic ordering and use it
//See ulib/FStar.LexicographicOrdering.fsti

open FStar.WellFounded
open FStar.LexicographicOrdering

unfold
let lt : binrel nat = fun x y -> x < y

unfold
let lt_dep (_:nat) : binrel nat = lt

let rec lt_well_founded (n:nat) : acc lt n =
  AccIntro (fun m _ -> lt_well_founded m)

let rec lt_dep_well_founded (m:nat) (n:nat) : acc (lt_dep m) n =
  AccIntro (fun p _ -> lt_dep_well_founded m p)

unfold
let nat_nat_lex_ordering
  : well_founded_relation (x:nat & nat)
  = lex lt_well_founded lt_dep_well_founded

type higher_nat : Type u#1 =
  | HZ : higher_nat
  | HS : higher_nat -> higher_nat

let higher_nat_lt
  : binrel u#1 u#0 higher_nat
  = fun x y -> x << y //sub-term ordering on higher nats

let rec higher_nat_lt_well_founded (n:higher_nat)
  : acc higher_nat_lt n
  = AccIntro (fun m _ -> higher_nat_lt_well_founded m)

let higher_nat_higher_nat_lex_order
  : well_founded_relation (x:higher_nat & higher_nat)
  = lex higher_nat_lt_well_founded (fun _ -> higher_nat_lt_well_founded)

let rec ackermann_wf (m n:nat)
  : Tot nat (decreases {:well-founded nat_nat_lex_ordering (| m, n |) })
  = if m = 0 then n + 1
    else if n = 0 then ackermann_wf (m - 1) 1
    else ackermann_wf (m - 1) (ackermann_wf m (n - 1))

assume
val get_previous (#a:Type) (r:well_founded_relation a) (x:a)
  : option (y:a { r y x })
  
let rec rel_parametric (r: nat -> well_founded_relation nat) (y:nat) (x:nat)
  : Tot nat (decreases {:well-founded r y x})
  = match get_previous (r y) x with
    | None -> 0
    | Some z -> 1 + rel_parametric r y z

module WFU = FStar.WellFounded.Util

//Since rel_poly can be polymorphically recursive in `a`
//the decreases clause is not type-correct on the recursively bound function
[@@expect_failure]
let rec rel_poly (a:Type) (r:well_founded_relation a) (x:a)
  : Tot nat (decreases {:well-founded r x})
  = 0


let rec rel_poly (a:Type) (r:binrel a) (wf_r:well_founded (WFU.squash_binrel r)) (x:a)
  : Tot nat (decreases {:well-founded WFU.lift_binrel_squashed_as_well_founded_relation wf_r (| a, x |)})
  = match get_previous (WFU.lift_binrel_squashed_as_well_founded_relation wf_r) (| a, x |) with
    | None -> 0
    | Some z -> 
      1 + rel_poly a r wf_r (dsnd z)


let rec rel_poly2 (a:Type) (r:binrel a) (wf_r:well_founded r) (x:a)
  : Tot nat (decreases {:well-founded WFU.lift_binrel_as_well_founded_relation wf_r (| a, x |)})
  = match get_previous (WFU.lift_binrel_as_well_founded_relation wf_r) (| a, x |) with
    | None -> 0
    | Some z ->
      WFU.elim_lift_binrel r z x;
      1 + rel_poly2 a r wf_r (dsnd z)
