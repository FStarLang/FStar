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
