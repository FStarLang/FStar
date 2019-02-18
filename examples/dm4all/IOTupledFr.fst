module IOTupledFr

(* GM: What's Fr? Free? *)
(* GM: Ah, context free, right? *)

open FStar.List
open FStar.WellFounded

type input = int
type output = int

noeq
type io a =
  | Read    : (input -> io a) -> io a
  | Write   : output -> io a -> io a
  | Return  : a -> io a

let post a = a * list output -> Type0
let wpty a = post a -> Type0

let return (a:Type u#a) (x:a) = Return x

let rec bind (a : Type u#aa) (b : Type u#bb)
         (l : io a) (k : a -> io b) : io b =
  match l with
  | Read f -> Read (fun i -> axiom1 f i; bind _ _ (f i) k)
  | Write o k' -> Write o (bind _ _ k' k)
  | Return v -> k v

let return_wp (a:Type) (x:a) : wpty a =
  fun p -> p (x, [])

let bind_wp (_ : range) (a:Type) (b:Type) (w : wpty a) (kw : a -> wpty b) : wpty b =
  fun p -> w (fun (x, l1) -> kw x (fun (y, l2) -> p (y, l1 @ l2)))
  
let rec interpretation #a (m : io a) (p : post a) : Type0 =
  match m with
  | Write o m -> interpretation m (fun (x, l) -> p (x, o :: l))
  | Read f -> forall (i : input). (axiom1 f i ; interpretation (f i) p)
  | Return x -> p (x, [])

total
reifiable
reflectable
new_effect {
  IO : a:Type -> Effect
  with
       repr      = io
     ; return    = return
     ; bind      = bind

     ; wp_type   = wpty
     ; return_wp = return_wp
     ; bind_wp   = bind_wp

     ; interp    = interpretation
}

val read : unit -> IO int (fun p -> forall x. p (x, []))
let read () =
    IO?.reflect (Read (fun i -> Return i))

val write : i:int -> IO unit (fun p -> p ((), [i]))
let write i =
    IO?.reflect (Write i (Return ()))

val test1 : unit -> IO int (fun p -> p (1, [2; 3]))
let test1 () =
  write 2;
  write 3;
  1
  
open FStar.Tactics

(* GM: For some reason I need to compute() in order to prove this *)
let test2 () : IO int (fun p -> p (1, [2; 3])) by (compute ()) =
  write 2;
  let x = read () in
  write 3;
  1

let test3 () : IO int (fun p -> forall x. p (1, [2; x])) by (compute ()) =
  write 2;
  let x = read () in
  let x = read () in
  let x = read () in
  let x = read () in
  write x;
  1

[@expect_failure]
let test4 () : IO int (fun p -> forall x. p (1, [x; x])) by (compute ()) =
  write 2;
  let x = read () in
  let x = read () in
  let x = read () in
  let x = read () in
  write x;
  1

let test5 () : IO int (fun p -> forall x. p (1, [x; x])) by (compute ()) =
  let x = read () in
  write x;
  write x;
  1
