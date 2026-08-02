module Alg

(*** Algebraic effects, now as a plain free monad. *** )

open FStar.Tactics.V2
open FStar.List.Tot
module L = Lattice

type state = int

type empty =

(* The set of operations. We keep an uninterpreted infinite set
of `Other` so we never rely on knowing all operations. *)
type op =
  | Read
  | Write
  | Raise
  | Other of int

assume val other_inp : int -> Type
let op_inp : op -> Type =
 function
 | Read -> unit
 | Write -> state
 | Raise -> exn
 | Other i -> other_inp i

assume val other_out : int -> Type
let op_out : op -> Type =
 function
 | Read -> state
 | Write -> unit
 | Raise -> empty
 | Other i -> other_out i

(* Free monad over `op`. *)
noeq
type tree0 (a:Type) : Type =
  | Return : a -> tree0 a
  | Op     : op:op -> i:(op_inp op) -> k:(op_out op -> tree0 a) -> tree0 a

type ops = list op
let sublist (l1 l2 : ops) = forall x. memP x l1 ==> memP x l2

(* Limiting the operations allowed in a tree. *)
let rec abides #a (labs:ops) (f : tree0 a) : prop =
  match f with
  | Op a i k -> a `memP` labs /\ (forall o. abides labs (k o))
  | Return _ -> True

type tree (a:Type) (labs : ops) : Type =
  r:(tree0 a){abides labs r}

(***** Some boring list lemmas *****)

let rec memP_at (l1 l2 : ops) (l : op)
  : Lemma (memP l (l1@l2) <==> (memP l l1 \/ memP l l2))
          [SMTPat (memP l (l1@l2))]
  = match l1 with
    | [] -> ()
    | _::l1 -> memP_at l1 l2 l

let rec sublist_at
  (l1 l2 : ops)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPatOr [[SMTPat (sublist l1 (l1@l2))];
                     [SMTPat (sublist l2 (l1@l2))]]]
  = match l1 with
    | [] -> ()
    | _::l1 -> sublist_at l1 l2

let rec abides_sublist_nopat #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2 c))
  = match c with
    | Return _ -> ()
    | Op a i k ->
      let sub o : Lemma (abides l2 (k o)) =
        abides_sublist_nopat l1 l2 (k o)
      in
      Classical.forall_intro sub

let abides_sublist #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2 c))
          [SMTPat (abides l2 c); SMTPat (sublist l1 l2)]
  = abides_sublist_nopat l1 l2 c

let widen #a (#labs1 #labs2 : ops) (c : tree a labs1)
  : Pure (tree a labs2)
         (requires sublist labs1 labs2)
         (ensures fun _ -> True)
  = c

let return_l #a (#labs:ops) (x:a) : tree a labs = Return x

(***** / boring list lemmas *****)

(* Folding a computation tree. The folding operation `h` need only be
   defined for the operations in the tree. *)
val fold_with (#a #b:_) (#labs : ops)
           (f:tree a labs)
           (v : a -> b)
           (h: (o:op{o `memP` labs} -> op_inp o -> (op_out o -> b) -> b))
           : b
let rec fold_with #a #b #labs f v h =
  match f with
  | Return x -> v x
  | Op act i k ->
    let k' (o : op_out act) : b = fold_with #_ #_ #labs (k o) v h in
    h act i k'

let handler_tree_op (o:op) (b:Type) (labs:ops) =
  op_inp o -> (op_out o -> tree b labs) -> tree b labs

let handler_tree (labs0 : ops) (b:Type) (labs1 : ops) : Type =
  o:op{o `memP` labs0} -> handler_tree_op o b labs1

val handle_tree (#a #b:_) (#labs0 #labs1 : ops)
           (f : tree a labs0)
           (v : a -> tree b labs1)
           (h : handler_tree labs0 b labs1)
           : tree b labs1
let handle_tree f v h = fold_with f v h

let return (a:Type) (x:a) : tree a [] = Return x

let bind (a b : Type) (#labs1 #labs2 : ops)
  (c : tree a labs1) (f : (x:a -> tree b labs2))
  : Tot (tree b (labs1@labs2))
  = sublist_at labs1 labs2;
    handle_tree #_ #_ #_ #(labs1@labs2) c f (fun act i k -> Op act i k)

let (let!) #a #b #labs1 #labs2 (m : tree a labs1) (f : a -> tree b labs2)
  : tree b (labs1@labs2)
  = bind a b m f

(* Mapping an algebraic operation into a monadic computation. *)
let geneff (o : op) (i : op_inp o) : tree (op_out o) [o] = Op o i Return

let get () : tree int [Read] = geneff Read ()
let put (s:state) : tree unit [Write] = geneff Write s
let raise #a (e:exn) : tree a [Raise] = Op Raise e (fun x -> match x with)

let rec listmap #a #b #labs (f : a -> tree b labs) (l : list a) : tree (list b) labs =
  match l with
  | [] -> return_l #labs []
  | x::xs -> let! y = f x in
             let! ys = listmap f xs in
             return_l #_ #[] (y :: ys)

let rec listmap_read #a #b #labs (f : a -> tree b labs) (l : list a)
  : tree (list b) (Read::labs) =
  match l with
  | [] -> let! _ = get () in return_l #labs []
  | x::xs -> let! _ = get () in
             let! y = f x in
             let! ys = listmap f xs in
             return_l #_ #[] (y :: ys)

(* Running pure trees/computations. *)
let frompure #a (t : tree a []) : a = match t with | Return x -> x
let run #a (f : unit -> tree a []) : a = frompure (f ())

exception Failure of string

let test0 (x y : int) : tree int [Read; Raise] =
  let! z = get () in
  if z < 0 then raise (Failure "error") else return_l #_ #[Raise] (x + y + z)

let test1 (x y : int) : tree int [Read; Raise; Write] =
  let! z = get () in
  if x + z > 0
  then widen #[Raise] #[Raise; Write] (raise (Failure "asd"))
  else let! _ = put 42 in return_l #_ #[] (y - z)

(* A simple operation-polymorphic add in monadic style. *)
let labpoly #labs (f g : unit -> tree int labs) : tree int (labs@labs) =
  let! x = f () in
  let! y = g () in
  return_l #_ #[] (x + y)

(* Explicitly defining catch on trees. *)
let rec __catch0 #a #labs (t1 : tree a (Raise::labs)) (t2 : tree a labs)
  : tree a labs
  = match t1 with
    | Op Raise e _ -> t2
    | Op act i k -> Op act i (fun o -> __catch0 (k o) t2)
    | Return v -> Return v

(* Equivalently via handle_tree. *)
let __catch1 #a #labs (t1 : tree a (Raise::labs)) (t2 : tree a labs)
  : tree a labs
  = handle_tree t1 (fun x -> Return x)
                   (function Raise -> fun _ _ -> t2
                           | op -> fun i k -> Op op i k)

let catch #a #labs (f : unit -> tree a (Raise::labs)) (g : unit -> tree a labs)
  : tree a labs
  = __catch1 (f ()) (g ())

let test_catch (f : unit -> tree int [Raise; Write]) : tree int [Write] =
  let g () : tree int [] = return int 42 in
  catch f g

let test_catch2 (f : unit -> tree int [Raise; Write]) : tree int [Raise; Write] =
  let g () : tree int [] = return int 42 in
  widen #[Write] #[Raise; Write] (catch f g)

(* Effectful-style handlers, now over plain trees. *)
let handler_op (o:op) (b:Type) (labs:ops) = op_inp o -> (op_out o -> tree b labs) -> tree b labs
let handler (labs0 : ops) (b:Type) (labs1 : ops) : Type = o:op{o `memP` labs0} -> handler_op o b labs1

let handle_with (#a #b:_) (#labs0 #labs1 : ops)
           (f : unit -> tree a labs0)
           (v : a -> tree b labs1)
           (h : handler labs0 b labs1)
   : tree b labs1
  = handle_tree (f ()) v h

let defh #b #labs (#o:op{o `memP` labs}) : handler_op o b labs =
  fun i k -> Op o i k

let try_with #a #labs (f : unit -> tree a (Raise::labs)) (g:unit -> tree a labs)
  : tree a labs
  = handle_with f (fun x -> return_l x)
                (function Raise -> fun _ _ -> g ()
                        | _     -> defh)

let some_as_alg (#a:Type) #labs : a -> tree (option a) labs = fun x -> return_l (Some x)

let catchE #a #labs (f : unit -> tree a (Raise::labs)) : tree (option a) labs =
  handle_with f some_as_alg (function Raise -> fun _ _ -> return_l None
                                   | _     -> defh)

let test_try_with (f : unit -> tree int [Raise; Write]) : tree int [Write] =
  let g () : tree int [] = return int 42 in
  try_with f g

(* Handling state. *)
let rec __catchST0 #a #labs (t1 : tree a (Read::Write::labs)) (s0:state) : tree (a & int) labs =
  match t1 with
  | Return v -> Return (v, s0)
  | Op Write s k -> __catchST0 (k ()) s
  | Op Read  _ k -> __catchST0 (k s0) s0
  | Op act i k -> Op act i (fun o -> __catchST0 (k o) s0)

let __catchST1_aux #a #labs (f : tree a (Read::Write::labs))
  : tree (state -> tree (a & state) labs) labs
  = handle_tree #_ #(state -> tree (a & state) labs)
                f
                (fun x -> Return (fun s0 -> Return (x, s0)))
                (function Read  -> fun _ k -> Return (fun s -> bind _ _ (k s)  (fun f -> f s))
                        | Write -> fun s k -> Return (fun _ -> bind _ _ (k ()) (fun f -> f s))
                        | act   -> fun i k -> Op act i k)

let __catchST1 #a #labs (f : tree a (Read::Write::labs)) (s0:state)
  : tree (a & state) labs
  = bind _ _ (__catchST1_aux f) (fun f -> f s0)

let catchST #a #labs (f: unit -> tree a (Read::Write::labs)) (s0:state)
  : tree (a & state) labs
  = __catchST1 (f ()) s0

let runST #a (f : unit -> tree a [Read; Write]) : state -> a & state =
  fun s0 -> run (fun () -> catchST f s0)

let run_stexn #a (f : unit -> tree a [Read; Write; Raise]) (s_0:state) : option (a & state) =
  run (fun () -> catchE (fun () -> catchST f s_0))

let run_exnst #a (f : unit -> tree a [Raise; Read; Write]) (s_0:state) : option a & state =
  run (fun () -> catchST (fun () -> catchE f) s_0)

(*** Interpreters into pure functions. ***)
let interp_pure_tree #a (t : tree a []) : Tot a = match t with | Return x -> x
let interp_pure #a (f : unit -> tree a []) : Tot a = interp_pure_tree (f ())

let rec interp_rd_tree #a (t : tree a [Read]) (s:state) : Tot a =
  match t with
  | Return x -> x
  | Op Read _ k -> interp_rd_tree (k s) s

let interp_rd #a (f : unit -> tree a [Read]) (s:state) : Tot a = interp_rd_tree (f ()) s

let rec interp_rdwr_tree #a (t : tree a [Read; Write]) (s:state) : Tot (a & state) =
  match t with
  | Return x -> (x, s)
  | Op Read _ k -> interp_rdwr_tree (k s) s
  | Op Write s k -> interp_rdwr_tree (k ()) s

let interp_rdwr #a (f : unit -> tree a [Read; Write]) (s:state) : Tot (a & state) = interp_rdwr_tree (f ()) s

let rec interp_read_raise_tree #a (t : tree a [Read; Raise]) (s:state) : either exn a =
  match t with
  | Return x -> Inr x
  | Op Read _ k -> interp_read_raise_tree (k s) s
  | Op Raise e _ -> Inl e

let interp_read_raise_exn #a (f : unit -> tree a [Read; Raise]) (s:state) : either exn a =
  interp_read_raise_tree (f ()) s
