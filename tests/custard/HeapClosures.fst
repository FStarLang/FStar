module HeapClosures
open FStar.All

(* Section 135, and FStarLang/FStar#4650.  On OCaml a function value is a heap
   closure that keeps every binder its F* type has, erased ones as [unit]; only
   a call to a top-level name drops arguments, and only the ones that
   definition's own parameters consume. *)

let pr (n:int) : ML unit = FStar.IO.print_string (string_of_int n ^ "\n")

let apply2 (#a #b #c:Type) (f: a -> b -> c) (x:a) (y:b) : c = f x y
let apply3 (#a #b #c #d:Type) (f: a -> b -> c -> d) (x:a) (y:b) (z:c) : d = f x y z

(* #4650: an effectful call whose only argument is erased. *)
let tick (#p : squash True) : ML unit = FStar.IO.print_string "tick\n"

(* #4650: a definition eta-reduced to another name. *)
type proof = squash True
let a (#p:proof) (x:int) : int = x
let f : (#p:squash True -> int -> int) = a

(* #4650: an arrow behind more abbreviations than the old limit of eight. *)
type t0 = (#p:squash True -> int -> int)
type t1 = unit -> t0
type t2 = unit -> t1
type t3 = unit -> t2
type t4 = unit -> t3
type t5 = unit -> t4
type t6 = unit -> t5
type t7 = unit -> t6
type t8 = unit -> t7
type t9 = unit -> t8
type t10 = unit -> t9
type t11 = unit -> t10
let deep : t11 = fun _ _ _ _ _ _ _ _ _ _ _ -> a
let deep8 : t8 = fun _ _ _ _ _ _ _ _ -> a

(* A top-level function stored where a closure of the same type is wanted. *)
let g (_:unit) (_:unit) : int = 42
let l : list (unit -> unit -> int) = [g; (fun () () -> 1)]

(* Partial applications that stop in front of an erased argument. *)
let h (u:unit) (x:int) (p:squash True) (v:unit) (y:int) : int = x + y
let pa : int -> squash True -> unit -> int -> int = h ()
let pb : list (unit -> int -> int) = [h () 1 (); (fun () y -> y)]

(* A definition returning a function: what it returns is a heap closure. *)
let k (x:int) : unit -> unit -> int = fun () () -> x
type ty = p:squash True -> int -> int
let m (x:int) : ty = fun (p:squash True) (y:int) -> x + y

(* Erased arguments of closures passed to polymorphic code. *)
let fs : int -> squash True -> int = fun x _ -> x + 1
let fg : int -> FStar.Ghost.erased int -> int = fun x _ -> x + 2

(* A record field and a constructor holding top-level functions. *)
noeq type ops = { op : x:int -> #p:squash True -> y:int -> int; unit_op : unit -> int }
let add (x:int) (#p:squash True) (y:int) : int = x + y
let seven () : int = 7
let r : ops = { op = add; unit_op = seven }
noeq type box = | Box : int -> squash True -> box
let unbox (b:box) : int = match b with Box n _ -> n

(* A local recursive function used as a closure. *)
let local_rec (n:int) : int =
  let rec go (#p:squash True) (i:int) (acc:int) : Tot int (decreases i) =
    if i <= 0 then acc else go #p (i - 1) (acc + i) in
  apply2 (go #()) n 0

(* The definition is not a lambda past its erased parameter, so it must not
   become a value evaluated once: each use has its own counter. *)
let counter (#p:squash True) : ML (unit -> ML int) =
  let r = alloc 0 in
  fun () -> r := !r + 1; !r

let main () : ML unit =
  tick #();
  tick #();
  pr (f #() 7);
  pr (deep () () () () () () () () () () () #() 11);
  pr (deep8 () () () () () () () () #() 8);
  pr (apply2 (List.hd l) () ());
  pr (apply2 (List.Tot.index l 1) () ());
  pr ((List.hd l) () ());
  pr (pa 3 () () 4);
  pr ((List.hd pb) () 5);
  pr (apply2 (h () 10 ()) () 2);
  pr (apply3 (fun (x:int) (u:unit) (y:int) -> h () x () u y) 20 () 2);
  pr (k 1 () ());
  pr (apply2 (k 2) () ());
  let c = k 3 in pr (c () ());
  pr (m 1 () 2);
  let lm : list ty = [m 5] in
  pr ((List.hd lm) () 6);
  pr (apply2 fs 1 ());
  pr (apply2 fg 1 (FStar.Ghost.hide 0));
  pr (apply2 #int #(squash True) (fun x _ -> x + 3) 1 ());
  pr (r.op 3 4 + r.unit_op ());
  pr (apply3 #int #(squash True) (fun x (_:squash True) y -> r.op x #() y) 30 () 4);
  let rop : int -> int -> int = fun x y -> r.op x y in
  pr (apply2 rop 30 5);
  let mk : int -> squash True -> box = Box in
  pr (unbox (apply2 mk 9 ()));
  pr (local_rec 4);
  let c1 = counter #() in
  pr (c1 ());
  pr (c1 ());
  pr (counter #() ())
