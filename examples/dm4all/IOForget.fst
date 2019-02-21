module IOForget

open FStar.List
open FStar.WellFounded

(* Reasoning about IO without the IO: we only care about the
 * final values, and treat input as a demonic non-determistic
 * choice. *)

type input = int
type output = int

noeq
type io a =
  | Read    : (input -> io a) -> io a
  | Write   : output -> io a -> io a
  | Return  : a -> io a

let wpty a = pure_wp a

let return (a:Type u#a) (x:a) = Return x

let rec bind (a : Type u#aa) (b : Type u#bb)
         (l : io a) (k : a -> io b) : io b =
  match l with
  | Read f -> Read (fun i -> axiom1 f i; bind _ _ (f i) k)
  | Write o k' -> Write o (bind _ _ k' k)
  | Return v -> k v

let rec interpretation #a (m : io a) (p : pure_post a) : Type0 =
  match m with
  | Write o m -> interpretation m p
  | Read f -> forall (i : input). (axiom1 f i ; interpretation (f i) p)
  | Return x -> p x

total
reifiable
reflectable
new_effect {
  IO : a:Type -> Effect
  with
       repr      = io
     ; return    = return
     ; bind      = bind

     ; wp_type   = pure_wp
     ; return_wp = pure_return
     ; bind_wp   = pure_bind_wp

     ; interp    = interpretation
}

val read : unit -> IO int (fun p -> forall x. p x)
let read () =
    IO?.reflect (Read (fun i -> Return i))

val write : i:int -> IO unit (fun p -> p ())
let write i =
    IO?.reflect (Write i (Return ()))

val test1 : unit -> IO int (fun p -> p 1)
let test1 () =
  write 2;
  write 3;
  1

open FStar.Tactics

let test2 () : IO int (fun p -> p 1) =
  write 2;
  let x = read () in
  write 3;
  1

let test3 () : IO int (fun p -> p 1) =
  write 2;
  let x = read () in
  let x = read () in
  let x = read () in
  let x = read () in
  write x;
  1

[@expect_failure]
let test4 () : IO int (fun p -> forall x. p 1) =
  write 2;
  let x = read () in
  let x = read () in
  let x = read () in
  let x = read () in
  write x;
  1

let test5 () : IO int (fun p -> p 1) =
  let x = read () in
  write x;
  write x;
  1

let ref = normalize_term (reify (test5 ()))
