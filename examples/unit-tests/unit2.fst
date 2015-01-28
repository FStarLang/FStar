module Unit2

(* GADTs *)
type t : Type -> Type = 
  | Int : i:int -> t int
  | Bool : b:bool -> t bool

let f (a:Type) (x:t a) : a = 
  match x with 
  | Int i -> i + 1
  | Bool b -> not b

  
(* Strategies:

  0. --rel1, the current default of F*
     Bidirectional type inference/checking
     Given a subtyping constraints ?u <: t, or t <: ?u, it solves this as ?u=t, eagerly!


  1. --rel2, as currently implemented in F*

     Infers subtyping constraints t <:n t', where n=0 for each
     constraint produced directly from the program

     As constraints decompose, e.g, t1 -> t1' <:n t2 -> t2', 
     produces t2 <:n+1 t1 and and t1' <:n+t t2'

     It delays the solving of ?u <:n t and t <:n ?u

     Then, solves ?u <:0 x:t{phi} as  ?u = t  /\ fun x -> phi
     for ?u <:n+1 t, solves it as ?u=t

  2. Slack variable idea

     Infers subtyping constraints t < t'
     It delays the solving of ?u < t and t <: ?u

     Then, solves ?u <: x:t{phi} as  ?u = x:t{phi /\ ?slack x}
                  x:t{phi} <: ?u as  ?u = x:t{phi \/ ?slack x}

  3. Flow-sensitive idea   (ideal)
     
     Infers subtyping constraints Psi |- t <: t', where Psi is the 
     It delays the solving of ?u < t and t <: ?u

     Then, solves ?u <: x:t{phi} as  ?u = x:t{phi /\ ?slack x}
                  x:t{phi} <: ?u as  ?u = x:t{phi \/ ?slack x}


 *)
(* Some simple tests that require --rel2 to succeed; to be expanded *)
let f1 (l:list nat) = 0::l    //succeeds with both 1 and 2
let f2 (x:nat) (y:int) = x=y
let f3 : list nat =
  let y = [0;1] in
  y

assume val f4 : nat -> Tot bool
let eta_f4 x = f4 x //fails under 1; succeeds under 2
(* assume val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b) *)
(* let eta_f4' = map (fun n -> f4 n) [2] //needs n:nat under strategy 1; works as is under 2 *)


assume val f: nat -> Tot bool
(* 
   under strategy 1, infers x:int -> Tot bool
   under strategy 2, infers x:nat -> Tot bool
 *)
let test x = if x >= 0 then f x else false
(* let test2 x = test x //succeeds only using 1 (and 3), not 2. *)

(* type pos = x:int{x>0} *)
(* let f g (l:list pos) (m:list nat) = map g l; map g m *)
assume val h: x:int -> u:unit{x > 0}

(* 
    x:int -> bool  (1)
    x:nat -> bool  (2)
 *)
let g x = h x; f4 x

(* works under (1) *)
(* fails under (2) *)
(* let g' x = g (-1) *)


