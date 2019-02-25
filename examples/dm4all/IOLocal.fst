module IOLocal

open FStar.List
open FStar.WellFounded

(* Reasoning about IO where the specs are over a list
 * of outputs corresponding to the history (the previously
 * outputted values) and postconditions over the "local" output,
 * (the output emitted by the program in question). *)

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
  | Read f -> Read (fun i -> axiom1 f i; bind _ _ (f i) k)
  | Write o k' -> Write o (bind _ _ k' k)
  | Return v -> k v

let h_trace = list output
let l_trace = list output

let post a = a -> l_trace -> Type0
(* flipping these arguments will break the gen_wps_for_free logic, FIXME *)
let wpty a = h_trace -> post a -> Type0

unfold
let return_wp (a:Type) (x:a) : wpty a =
  fun h p -> p x []

unfold
let bind_wp (_ : range) (a:Type) (b:Type) (w : wpty a) (kw : a -> wpty b) : wpty b =
  fun h p -> w h (fun x l -> kw x (h @ l) (fun y l' -> p y (l @ l')))

let rec interpretation #a (m : io a) (h : list output) (p : post a) : Type0 =
  match m with
  | Write o m -> interpretation m (h @ [o]) (fun x l -> p x (o :: l))
  | Read f -> forall (i : input). (axiom1 f i ; interpretation (f i) h p)
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

val read : unit -> IO int (fun h p -> forall x. p x [])
let read () =
    IO?.reflect (Read (fun i -> Return i))

(* Keeping the log backwards, since otherwise the VCs are too contrived for z3.
 * Likely something we should fix separately.. *)

val write : o:int -> IO unit (fun h p -> p () [o])
let write i =
    IO?.reflect (Write i (Return ()))

val need_a_1 : unit -> IO int (fun h p -> List.memP 1 h /\ p 42 [])
let need_a_1 () = 42

open FStar.Tactics

(* GM: This stupid length precondition only there to help z3. If we flip
 * the ordering on the history list, then this works like a charm but test9
 * below starts displaying the same bad behaviour.
 *
 * This works without this condition in IOHist.fst. I believe since there
 * the order is flipped. *)
let test_hist_1 () : IO unit (fun h p -> List.length h <= 5 /\ p () [1]) =
  write 1;
  let _ = need_a_1 () in
  ()

[@expect_failure]
let test_hist_2 () : IO unit (fun h p -> List.length h <= 5 /\ p () [1]) =
  let _ = need_a_1 () in
  write 1;
  ()

let test1 () : IO int (fun h p -> p 1 [2;3]) =
  write 2;
  write 3;
  1

let test2 () : IO int (fun h p -> p 1 [2;3]) =
  write 2;
  let x = read () in
  write 3;
  1

[@expect_failure]
let test4 () : IO int (fun h p -> forall x. p 1 [x;x]) =
  write 2;
  let x = read () in
  let x = read () in
  let x = read () in
  let x = read () in
  write x;
  1

let test5 () : IO int (fun h p -> forall x. p 1 [x;x]) =
  let x = read () in
  write x;
  write x;
  1

effect Io (a:Type) (pre':h_trace -> Type0) (post':h_trace -> a -> l_trace -> Type0) =
        IO a (fun h p -> pre' h /\ (forall r l . post' h r l ==> p r l))

let test6 () : Io int (fun _ -> True) (fun h x l -> x = 1 /\ (exists y . l = [y;y])) =
  let x = read () in
  write x;
  write x;
  1

let test7 (b:bool) 
  : Io int (fun _ -> True) 
           (fun h x l -> x = 1 /\ (exists y . l = [y;y] \/ l = [y+1;y])) =
  let x = read () in
  (if b 
   then write (x + 1)
   else write x);
  write x;
  1

let test8 (b:bool) 
  : Io int (fun _ -> True) 
           (fun h x l -> x = 1 /\ (exists y z . z < y /\ l = [y;z])) =
  let x = read () in
  (if b 
   then write (x + 1)
   else write x);
  write (x - 1);
  1

let rec n_writes (n:nat) (i:int) = 
  if n = 0 
  then []
  else i :: n_writes (n - 1) i

let rec test9 (n:nat) (i:int)
  : Io unit (requires (fun _     -> True)) 
            (ensures  (fun h x l -> l = n_writes n i)) = 
  if n = 0
  then ()
  else (write i; test9 (n - 1) i)

let test10 (h0:h_trace) 
  : Io unit (requires (fun h -> h = h0))
            (ensures  (fun h _ l -> h = h0 /\ length l > 1)) =
  write 24;
  let x = read () in
  write 42
