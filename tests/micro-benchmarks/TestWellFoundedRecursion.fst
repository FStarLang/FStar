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
  | SCons: _:unit -> f:(unit -> stream a) -> stream a

let rec fmap_stream (#a #b:Type) (f:a -> b) (x:stream a) : stream b =
  match x with
  | SNil -> SNil
  | SCons h t ->
    let ft () = fmap_stream f (t ()) in
    SCons () ft
