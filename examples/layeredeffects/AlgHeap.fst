module AlgHeap

(* Algebraic heap example, now as a plain free monad rather than a layered effect. *)

open FStar.Tactics.V2
open FStar.List.Tot
module Map = FStar.Map

type loc = int
type state = Map.t loc int

type empty =

type op =
  | Read
  | Write
  | Raise
  | Other of int

assume val other_inp : int -> Type
let op_inp : op -> Type = function
 | Read -> unit
 | Write -> state
 | Raise -> exn
 | Other i -> other_inp i

assume val other_out : int -> Type
let op_out : op -> Type = function
 | Read -> state
 | Write -> unit
 | Raise -> empty
 | Other i -> other_out i

noeq
type tree0 (a:Type) : Type =
  | Return : a -> tree0 a
  | Op     : op:op -> i:(op_inp op) -> k:(op_out op -> tree0 a) -> tree0 a

type ops = list op
let sublist (l1 l2 : ops) = forall x. memP x l1 ==> memP x l2

let rec abides #a (labs:ops) (f : tree0 a) : prop =
  match f with
  | Op a i k -> memP a labs /\ (forall o. abides labs (k o))
  | Return _ -> True

type tree (a:Type) (labs : ops) : Type = r:(tree0 a){abides labs r}

let rec sublist_at (l1 l2 : ops)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPatOr [[SMTPat (sublist l1 (l1@l2))]; [SMTPat (sublist l2 (l1@l2))]]]
  = match l1 with | [] -> () | _::l1 -> sublist_at l1 l2

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
  : Pure (tree a labs2) (requires sublist labs1 labs2) (ensures fun _ -> True)
  = c

let return_l #a (#labs:ops) (x:a) : tree a labs = Return x

val fold_with (#a #b:_) (#labs : ops)
           (f:tree a labs)
           (v : a -> b)
           (h: (o:op{o `memP` labs} -> op_inp o -> (op_out o -> b) -> b))
           : b
let rec fold_with #a #b #labs f v h =
  match f with
  | Return x -> v x
  | Op act i k -> h act i (fun o -> fold_with #_ #_ #labs (k o) v h)

let handler_tree_op (o:op) (b:Type) (labs:ops) =
  op_inp o -> (op_out o -> tree b labs) -> tree b labs
let handler_tree (labs0 : ops) (b:Type) (labs1 : ops) : Type =
  o:op{o `memP` labs0} -> handler_tree_op o b labs1

val handle_tree (#a #b:_) (#labs0 #labs1 : ops)
           (f:tree a labs0)
           (v : a -> tree b labs1)
           (h: handler_tree labs0 b labs1)
           : tree b labs1
let handle_tree f v h = fold_with f v h

let return (a:Type) (x:a) : tree a [] = Return x
let bind (a b : Type) (#labs1 #labs2 : ops) (c : tree a labs1) (f : (x:a -> tree b labs2))
  : Tot (tree b (labs1@labs2))
  = sublist_at labs1 labs2;
    handle_tree #_ #_ #labs1 #(labs1@labs2) c f (fun act i k -> Op act i k)

let (let!) #a #b #labs1 #labs2 (m : tree a labs1) (f : a -> tree b labs2)
  : tree b (labs1@labs2) = bind a b m f

let get () : tree state [Read] = Op Read () Return
let put (s:state) : tree unit [Write] = Op Write s Return
let raise #a (e:exn) : tree a [Raise] = Op Raise e (fun x -> match x with)

let rec interp_rdwr_tree #a (t : tree a [Read;Write]) (s:state) : Tot (a & state) =
  match t with
  | Return x -> (x, s)
  | Op Read _ k -> interp_rdwr_tree (k s) s
  | Op Write s k -> interp_rdwr_tree (k ()) s

let interp_as_fun #a (t : tree a [Read;Write]) : state -> a & state = interp_rdwr_tree t

let sel (r:loc) : tree int [Read] =
  let! h = get () in
  return_l #_ #[] (Map.sel h r)

let upd (r:loc) (v:int) : tree unit [Read;Write] =
  let! h = get () in
  put (Map.upd h r v)

let (!) = sel
let (:=) = upd

let addx (l:loc) (x:int) : tree unit [Read;Read;Write] =
  let! v = !l in
  l := v + x

let swap (l1 l2 : loc) : tree unit [Read;Read;Read;Write;Read;Write] =
  let! r1 = !l1 in
  let! r2 = !l2 in
  let! _ = l1 := r2 in
  l2 := r1
