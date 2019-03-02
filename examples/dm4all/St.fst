module St

(* Reasoning about state in the canonical way. *)

type state = int

let st a = state -> a * state

let return (a:Type) (x:a) : st a = fun s -> (x, s)

let bind (a b : Type) (m : st a) (f : a -> st b) : st b =
  fun s -> let (v, s') = m s in f v s'

let post a = a -> state -> Type0
let wpty a = state -> post a -> Type0

let return_wp (a:Type) (x:a) : wpty a =
  fun h p -> p x h

unfold
let bind_wp (_ : range) (a:Type) (b:Type) (w : wpty a) (kw : a -> wpty b) : wpty b =
  fun h p -> w h (fun x h' -> kw x h' (fun y h'' -> p y h''))

let interpretation #a (m : st a) (s0 : state) (p : post a) : Type0 =
  let (x, s1) = m s0 in p x s1

total
reifiable
reflectable
new_effect {
  St : a:Type -> Effect
  with
       repr      = st
     ; return    = return
     ; bind      = bind

     ; wp_type   = wpty
     ; return_wp = return_wp
     ; bind_wp   = bind_wp

     ; interp    = interpretation
}

(* Actions *)
val get : unit -> St state (fun s p -> p s s)
let get () =
  St?.reflect (fun s -> (s,s))

val set : s:state -> St unit (fun _ p -> p () s)
let set s =
  St?.reflect (fun _ -> ((), s))

val modify (f : state -> state) : St unit (fun s p -> p () (f s))
let modify f =
    let s = get () in
    set (f s)

let test1 () : St int (fun s0 p -> p 42 (s0 + 5)) =
  let x = get () in
  set (x + 2);
  let y = get () in
  set (y + 3);
  42

let test2 () : St int (fun s0 p -> s0 >= 1 /\ p (s0 + 2) (s0 + 5)) =
  let x = get () in
  set (x + 2);
  let y = get () in
  set (y + 3);
  y

let test3 () : St int (fun s0 p -> forall x s1. p x s1) =
  let x = get () in
  set (1 + x `op_Multiply` x);
  test2 ()
  
(* This fails since we cannot prove test2's precondition,
 * i.e. that the state is >= 1 *)
[@expect_failure]
let test4 () : St int (fun s0 p -> forall x s1. p x s1) =
  let x = get () in
  set (x `op_Multiply` x);
  test2 ()
