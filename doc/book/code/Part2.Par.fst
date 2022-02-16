module Part2.Par
open FStar.Classical.Sugar

noeq
type action_class = {
  t : Type;
  input_of : t -> Type;
  output_of : t -> Type;
}

//SNIPPET_START: tree$
noeq
type tree (acts:action_class) (a:Type) =
  | Return : x:a -> tree acts a
  | DoThen : act:acts.t ->
             input:acts.input_of act ->
             continue: (acts.output_of act -> tree acts a) ->
             tree acts a
  | Or :  tree acts a -> tree acts a -> tree acts a
//SNIPPET_END: tree$

//SNIPPET_START: return and bind$
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
//SNIPPET_END: return and bind$  

//SNIPPET_START: par$
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
//SNIPPET_END: par$

////////////////////////////////////////////////////////////////////////////////

type rw =
  | Read
  | Write

let input_of : rw -> Type =
  fun a ->
    match a with
    | Read -> unit
    | Write -> int

let output_of : rw -> Type =
  fun a ->
    match a with
    | Read -> int
    | Write -> unit

let rw_actions = { t = rw; input_of ; output_of }

//SNIPPET_START: interp$
let randomness = nat -> bool
let par_st a = randomness -> pos:nat -> s0:int -> (a & int & nat)
let rec interp #a (f:tree rw_actions a) 
  : par_st a 
  = fun rand pos s0 ->
      match f with
      | Return x -> x, s0, pos
      | DoThen Read _ k -> interp (k s0) rand pos s0
      | DoThen Write s1 k -> interp (k ()) rand pos s1      
      | Or l r -> 
        if rand pos
        then interp l rand (pos + 1) s0
        else interp r rand (pos + 1) s0
let st a = int -> a & int
let interpret #a (f:tree rw_actions a) 
  : st a    
  = fun s0 -> 
      let x, s, _ = interp f (fun n -> n % 2 = 0) 0 s0 in 
      x, s
//SNIPPET_END: interp$

//SNIPPET_START: sample program$
let read : tree rw_actions int = DoThen Read () Return
let write (x:int) : tree rw_actions unit = DoThen Write x Return
let inc
  : tree rw_actions unit
  = x <-- read ;
    write (x + 1)
let par_inc = par inc inc 
//SNIPPET_END: sample program$

//SNIPPET_START: test_par_inc$
let test_prog = assert_norm (forall x. snd (interpret par_inc x) == x + 1)
//SNIPPET_END: test_par_inc$

//SNIPPET_START: atomic increment$
type rwi =
  | R
  | W
  | Inc
  
let input_of_rwi : rwi -> Type =
  fun a ->
    match a with
    | R -> unit
    | W -> int
    | Inc -> unit

let output_of_rwi : rwi -> Type =
  fun a ->
    match a with
    | R -> int
    | W -> unit
    | Inc -> unit

let rwi_actions = { t = rwi; input_of=input_of_rwi ; output_of=output_of_rwi }

let atomic_inc : tree rwi_actions unit = DoThen Inc () Return

let rec interp_rwi #a (f:tree rwi_actions a) 
  : par_st a 
  = fun tape pos s0 ->
      match f with
      | Return x -> x, s0, pos
      | DoThen R _ k -> interp_rwi (k s0) tape pos s0
      | DoThen W s1 k -> interp_rwi (k ()) tape pos s1      
      | DoThen Inc () k -> interp_rwi (k ()) tape pos (s0 + 1)            
      | Or l r -> 
        let b = tape pos in
        if b
        then interp_rwi l tape (pos + 1) s0
        else interp_rwi r tape (pos + 1) s0
let interpret_rwi #a (f:tree rwi_actions a) 
  : st a    
  = fun s0 -> 
      let x, s, _ = interp_rwi f (fun n -> n % 2 = 0) 0 s0 in 
      x, s

let par_atomic_inc = par atomic_inc atomic_inc
let test_par_atomic_inc = assert_norm (forall x. snd (interpret_rwi par_atomic_inc x) == x + 2)
//SNIPPET_END: atomic increment$



