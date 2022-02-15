module Part2.Par
open FStar.Classical.Sugar
let state : Type = int

type action =
  | Read
  | Write

let input_of : action -> Type =
  fun a ->
    match a with
    | Read -> unit
    | Write -> state

let output_of : action -> Type =
  fun a ->
    match a with
    | Read -> state
    | Write -> unit

noeq
type m (a:Type) =
  | Return : x:a -> m a
  | DoThen : act:action ->
             input:input_of act ->
             continue: (output_of act -> m a) ->
             m a
  | Or :  m a -> m a -> m a

let return #a (x:a)
  : m a
  = Return x

let rec bind #a #b (f: m a) (g: a -> m b)
  : m b
  = match f with
    | Return x -> g x
    | DoThen act i k ->
      DoThen act i (fun x -> bind (k x) g)
    | Or m0 m1 -> Or (bind m0 g) (bind m1 g)
  
let rec l_par #a #b (f:m a) (g:m b)
  : m (a & b)
  = match f with
    | Return v -> x <-- g; return (v, x)
    | DoThen a i k ->
      DoThen a i (fun x -> r_par (k x) g)
    | Or m0 m1 -> Or (l_par m0 g) (l_par m1 g)

and r_par #a #b (f:m a) (g: m b)
  : m (a & b)
  = match g with
    | Return v -> x <-- f; return (x, v)
    | DoThen a i k ->
      DoThen a i (fun x -> l_par f (k x))
    | Or m0 m1 -> Or (r_par f m0) (l_par f m1)

let par #a #b (f: m a) (g: m b)
  : m (a & b)
  = Or (l_par f g) (r_par f g)

let randomness = nat -> bool
let par_st a = randomness -> pos:nat -> s0:state -> (a & state & nat)
let rec interp #a (f:m a) 
  : par_st a 
  = fun tape pos s0 ->
      match f with
      | Return x -> x, s0, pos
      | DoThen Read _ k -> interp (k s0) tape pos s0
      | DoThen Write s1 k -> interp (k ()) tape pos s1      
      | Or l r -> 
        let b = tape pos in
        if b
        then interp l tape (pos + 1) s0
        else interp r tape (pos + 1) s0

let tape = fun n -> n%2 = 0
let read : m state = DoThen Read () Return
let write (x:state) : m unit = DoThen Write x Return
let inc
  : m unit
  = x <-- read ;
    write (x + 1)

let prog = par inc inc //interprets to 1
