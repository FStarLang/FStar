module IORWFree

(* Reasoning about IO, considering both inputs and outputs on the
 * trace, without access to the history of events. *)

type input = int
type output = int

noeq
type io a =
  | Read    : (input -> io a) -> io a
  | Write   : output -> io a -> io a
  | Return  : a -> io a

let return (a:Type u#a) (x:a) = Return x

let rec bind (a : Type u#aa) (b : Type u#bb)
         (l : io a) (k : a -> io b) : io b =
  match l with
  | Read f -> Read (fun i -> FStar.WellFounded.axiom1 f i; bind _ _ (f i) k)
  | Write o k' -> Write o (bind _ _ k' k)
  | Return v -> k v

type event =
  | In  : input -> event
  | Out : output -> event

let h_trace = list event
let l_trace = list event

let post a = a -> l_trace -> Type0
let wpty a = post a -> Type0

unfold
let return_wp (a:Type) (x:a) : wpty a =
  fun p -> p x []

unfold
let bind_wp (_ : range) (a:Type) (b:Type) (w : wpty a) (kw : a -> wpty b) : wpty b =
  fun p -> w (fun x l -> kw x (fun y l' -> p y (l @ l')))

let rec interpretation #a (m : io a) (p : post a) : Type0 =
  match m with
  | Write o m -> interpretation m (fun x l -> p x ((Out o) :: l))
  | Read f -> forall (i : input). (FStar.WellFounded.axiom1 f i;
                                   interpretation (f i) (fun x l -> p x ((In i) :: l)))
  | Return x -> p x []

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

     ; interp = interpretation
}

val read : unit -> IO int (fun p -> forall x. p x [In x])
let read () =
    IO?.reflect (Read (fun i -> Return i))

val write : o:int -> IO unit (fun p -> p () [Out o])
let write i =
    IO?.reflect (Write i (Return ()))

let test1 () : IO int (fun p -> p 1 [Out 2; Out 3]) =
  write 2;
  write 3;
  1

let test2 () : IO int (fun p -> forall i . p 1 [Out 2; In i; Out 3]) =
  write 2;
  let x = read () in
  write 3;
  1

effect Io (a:Type) (pre':Type0) (post':a -> l_trace -> Type0) =
        IO a (fun p -> pre' /\ (forall r l . post' r l ==> p r l))

let test3 (i:int)
  : Io int (requires True)
           (ensures  (fun x l -> exists x . l = [Out i; In x; Out x])) =
  write i;
  let x = read () in
  write x;
  1

let rec n_w_events (n:nat) (i:int) =
  if n = 0
  then []
  else Out i :: n_w_events (n - 1) i

let rec test4 (n:nat) (i:int)
  : Io unit (requires True)
            (ensures  (fun x l -> l = n_w_events n i)) =
  if n = 0
  then ()
  else (write i; test4 (n - 1) i)

val duplicate : unit -> IO unit (fun p -> forall x. p () [In x; Out x; Out x])
let duplicate () =
    let c = read () in
    write c;
    write c
