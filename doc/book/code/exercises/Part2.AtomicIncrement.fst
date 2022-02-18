module Part2.AtomicIncrement
open FStar.Classical.Sugar

noeq
type action_class = {
  t : Type;
  input_of : t -> Type;
  output_of : t -> Type;
}

noeq
type tree (acts:action_class) (a:Type) =
  | Return : x:a -> tree acts a
  | DoThen : act:acts.t ->
             input:acts.input_of act ->
             continue: (acts.output_of act -> tree acts a) ->
             tree acts a
  | Or :  tree acts a -> tree acts a -> tree acts a

let return #acts #a (x:a)
  : tree acts a
  = Return x

let rec bind #acts #a #b (f: tree acts a) (g: a -> tree acts b)
  : tree acts b
  = match f with
    | Return x -> g x
    | DoThen act i k ->
      DoThen act i (fun x -> bind (k x) g)
    | Or m0 m1 -> Or (bind m0 g) (bind m1 g)

let rec l_par #acts #a #b (f:tree acts a) (g:tree acts b)
  : tree acts (a & b)
  = match f with
    | Return v -> x <-- g; return (v, x)
    | DoThen a i k ->
      DoThen a i (fun x -> r_par (k x) g)
    | Or m0 m1 -> Or (l_par m0 g) (l_par m1 g)

and r_par #acts #a #b (f:tree acts a) (g: tree acts b)
  : tree acts (a & b)
  = match g with
    | Return v -> x <-- f; return (x, v)
    | DoThen a i k ->
      DoThen a i (fun x -> l_par f (k x))
    | Or m0 m1 -> Or (r_par f m0) (r_par f m1)

let par #acts #a #b (f: tree acts a) (g: tree acts b)
  : tree acts (a & b)
  = Or (l_par f g) (r_par f g)

type rwi =
  | R
  | W
  | Inc

let input_of_rwi : rwi -> Type = admit()
let output_of_rwi : rwi -> Type = admit()
let rwi_actions = { t = rwi; input_of=input_of_rwi ; output_of=output_of_rwi }

let atomic_inc : tree rwi_actions unit = admit()
let randomness = nat -> bool
let par_st a = randomness -> pos:nat -> s0:int -> (a & int & nat)

let rec interp_rwi #a (f:tree rwi_actions a)
  : par_st a
  = admit()
let st a = int -> a & int
let interpret_rwi #a (f:tree rwi_actions a)
  : st a
  = admit()
let par_atomic_inc = par atomic_inc atomic_inc
[@@expect_failure] //remove this and make the assertion below succeed
let test_par_atomic_inc =
  assert_norm (forall x. snd (interpret_rwi par_atomic_inc x) == x + 2)
