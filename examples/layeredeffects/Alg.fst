module Alg

(*** Algebraic effects. ***)

open Common
open FStar.Tactics
open FStar.List.Tot
open FStar.Universe
module WF = FStar.WellFounded
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
 | Other i -> other_inp i

(* Free monad over `op` *)
noeq
type tree0 (a:Type u#aa) : Type u#aa =
  | Return : a -> tree0 a
  | Op     : op:op -> i:(op_inp op) -> k:(op_out op -> tree0 a) -> tree0 a

type ops = list op
let sublist (l1 l2 : ops) = forall x. memP x l1 ==> memP x l2

(* Limiting the operations allowed in a tree *)
let rec abides #a (labs:ops) (f : tree0 a) : prop =
  begin match f with
  | Op a i k -> a `memP` labs /\ (forall o. (WF.axiom1 k o; abides labs (k o)))
  | Return _ -> True
  end

(* Refined free monad *)
type tree (a:Type u#aa) (labs : list u#0 op)
  : Type u#aa
  = r:(tree0 a){abides labs r}

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

let sublist_at_self (l : ops)
  : Lemma (sublist l (l@l))
          [SMTPat (sublist l (l@l))]
  = ()
  
let rec abides_sublist_nopat #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2) c)
  = match c with
    | Return _ -> ()
    | Op a i k ->
      let sub o : Lemma (abides l2 (k o)) =
        FStar.WellFounded.axiom1 k o;
        abides_sublist_nopat l1 l2 (k o)
      in
      Classical.forall_intro sub

let abides_sublist #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2 c))
          [SMTPat (abides l2 c); SMTPat (sublist l1 l2)]
  = abides_sublist_nopat l1 l2 c

let abides_at_self #a
  (l : ops)
  (c : tree0 a)
  : Lemma (abides (l@l) c <==>  abides l c)
          [SMTPat (abides (l@l) c)]
  = (* Trigger some patterns *)
    assert (sublist l (l@l));
    assert (sublist (l@l) l)

let abides_app #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c \/ abides l2 c))
          (ensures (abides (l1@l2) c))
          [SMTPat (abides (l1@l2) c)]
  = sublist_at l1 l2

(***** / boring list lemmas *****)

(* Folding a computation tree. The folding operation `h` need only be
defined for the operations in the tree. We also take a value case
so this essentially has a builtin 'map' as well. *)
val fold_with (#a #b:_) (#labs : ops)
           (f:tree a labs)
           (v : a -> b)
           (h: (o:op{o `memP` labs} -> op_inp o -> (op_out o -> b) -> b))
           : b
let rec fold_with #a #b #labs f v h =
  match f with
  | Return x -> v x
  | Op act i k ->
    let k' (o : op_out act) : b =
       WF.axiom1 k o;
       fold_with #_ #_ #labs (k o) v h
    in
    h act i k'

(* A (tree) handler for a single operation *)
let handler_tree_op (o:op) (b:Type) (labs:ops) =
  op_inp o -> (op_out o -> tree b labs) -> tree b labs

(* A (tree) handler for an operation set *)
let handler_tree (labs0 : ops) (b:Type) (labs1 : ops) : Type =
  o:op{o `memP` labs0} -> handler_tree_op o b labs1

(* The most generic handling construct, we use it to implement bind.
It is actually just a special case of folding. *)
val handle_tree (#a #b:_) (#labs0 #labs1 : ops)
           ($f : tree a labs0)
           (v : a -> tree b labs1)
           (h : handler_tree labs0 b labs1)
           : tree b labs1
let handle_tree f v h = fold_with f v h

let return (a:Type) (x:a)
  : tree a []
  = Return x

let bind (a b : Type)
  (#labs1 #labs2 : ops)
  (c : tree a labs1)
  (f : (x:a -> tree b labs2))
  : Tot (tree b (labs1@labs2))
  = handle_tree #_ #_ #_ #(labs1@labs2) c f (fun act i k -> Op act i k)
  
let subcomp (a:Type)
  (#labs1 #labs2 : ops)
  (f : tree a labs1)
  : Pure (tree a labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let if_then_else
  (a : Type)
  (#labs1 #labs2 : ops)
  (f : tree a labs1)
  (g : tree a labs2)
  (p : bool)
  : Type
  = tree a (labs1@labs2)

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  Alg : a:Type -> ops  -> Effect
  with
  repr         = tree;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let lift_pure_alg
 (a:Type)
 (wp : pure_wp a)
 (f : eqtype_as_type unit -> PURE a wp)
 : Pure (tree a [])
        (requires (wp (fun _ -> True)))
        (ensures (fun _ -> True))
 = let v = elim_pure f (fun _ -> True) in
   Return v

sub_effect PURE ~> Alg = lift_pure_alg

(* Mapping an algebraic operation into an effectful computation. *)
let geneff (o : op) (i : op_inp o)
  : Alg (op_out o) [o]
  = Alg?.reflect (Op o i Return)

let get   : unit    ->    Alg int [Read]     = geneff Read
let put   : state   ->    Alg unit [Write] = geneff Write
let raise : #a:_ -> exn -> Alg a [Raise]    = fun e -> match geneff Raise e with

let another_raise #a (e:exn) : Alg a [Raise] =  
  // Funnily enough, the version below succeeds from concluding `a ==
  // empty` under the lambda since the context becomes inconsistent. All
  // good, just surprising.
  Alg?.reflect (Op Raise e Return)

(* Running pure trees *)
let frompure #a (t : tree a []) : a = match t with | Return x -> x

(* Running pure computations *)
let run #a (f : unit -> Alg a []) : a = frompure (reify (f ()))

exception Failure of string

let test0 (x y : int) : Alg int [Read; Raise] =
  let z = get () in
  if z < 0 then raise (Failure "error");
  x + y + z

let test1 (x y : int) : Alg int [Raise; Read; Write] =
  let z = get () in
  if x + z > 0
  then raise (Failure "asd")
  else (put 42; y - z)

(* A simple operation-polymorphic add in direct style *)
let labpoly #labs (f g : unit -> Alg int labs) : Alg int labs = f () + g ()

// FIXME: putting this definition inside catch causes a blowup:
//
// Unexpected error
// Failure("Empty option")
// Raised at file "stdlib.ml", line 29, characters 17-33
// Called from file "ulib/ml/FStar_All.ml" (inlined), line 4, characters 21-24
// Called from file "src/ocaml-output/FStar_TypeChecker_Util.ml", line 874, characters 18-65
// Called from file "src/ocaml-output/FStar_TypeChecker_Common.ml", line 675, characters 34-38
// Called from file "src/ocaml-output/FStar_TypeChecker_Common.ml", line 657, characters 25-33
// Called from file "src/ocaml-output/FStar_TypeChecker_TcTerm.ml", line 2048, characters 30-68
// Called from file "src/basic/ml/FStar_Util.ml", line 24, characters 14-18
// ....

(* Explicitly defining catch on trees *)
let rec __catch0 #a #labs (t1 : tree a (Raise::labs)) (t2 : tree a labs)
  : tree a labs
  = match t1 with
    | Op Raise e _ -> t2
    | Op act i k ->
      let k' o : tree a labs =
        WF.axiom1 k o;
        __catch0 (k o) t2
      in
      Op act i k'
    | Return v -> Return v

(* Equivalently via handle_tree *)
let __catch1 #a #labs (t1 : tree a (Raise::labs)) (t2 : tree a labs)
  : tree a labs
  = handle_tree t1 (fun x -> Return x) 
                   (function Raise -> fun i k -> t2
                           | op -> fun i k -> Op op i k)

(* Lifting it into the effect *)
let catch #a #labs (f : unit -> Alg a (Raise::labs)) (g : unit -> Alg a labs)
  : Alg a labs
  = Alg?.reflect (__catch1 (reify (f ())) (reify (g ())))

(* Example: get rid of the Raise *)
let test_catch #labs (f : unit -> Alg int [Raise; Write]) : Alg int [Write] =
  let g () : Alg int [] = 42 in
  catch f g

(* Or keep it... Koka-style *)
let test_catch2 (f : unit -> Alg int [Raise; Write]) : Alg int [Raise; Write] =
  let g () : Alg int [] = 42 in
  catch f g

(* But of course, we have to handle if it is not in the output. *)
[@@expect_failure [19]]
let test_catch3 (f : unit -> Alg int [Raise; Write]) : Alg int [Write] =
  let g () : Alg int [Raise] = raise (Failure "hmm") in
  catch f g

(***** Now for the effectful version *****)

(* An (effectful) handler for a single operation *)
let handler_op (o:op) (b:Type) (labs:ops) = op_inp o -> (op_out o -> Alg b labs) -> Alg b labs

(* An (effectful) handler for an operation set *)
let handler (labs0 : ops) (b:Type) (labs1 : ops) : Type = o:op{o `memP` labs0} -> handler_op o b labs1

(* The generic effectful handling operation, defined simply by massaging
handle_tree into the Alg effect. *)
let handle_with (#a #b:_) (#labs0 #labs1 : ops)
           ($f : unit -> Alg a labs0)
           (v : a -> Alg b labs1)
           (h : handler labs0 b labs1)
           (* Looking at v and h together, they basically represent
            * a handler type [ a<labs0> ->> b<labs1> ] from other
            * languages. *)
   : Alg b labs1
  = Alg?.reflect (handle_tree (reify (f ()))
                              (fun x -> reify (v x))
                              (fun a i k -> reify (h a i (fun o -> Alg?.reflect (k o)))))

(* A default case for handlers. With the side condition that the
operation we're defaulting will remain in the tree, so it has to be in
`labs`. All arguments are implicit, F* can usually figure `op` out. *)
let defh #b #labs (#o:op{o `memP` labs})
  : handler_op o b labs
  = fun i k -> k (geneff o i)

(* The version taking the operation explicitly. *)
let exp_defh #b #labs
  : handler labs b labs
  = fun o i k -> k (geneff o i)
  // Or: = fun _ -> defh

(* Of course this can also be done for trees *)
let defh_tree #b #labs (#o:op{o `memP` labs})
  : handler_tree_op o b labs
  = fun i k -> Op o i k

(* Another version of catch, but directly in the effect. Note that we do
not build Op nor Return nodes, but work in a more direct style. For the
default case, we just call the operation op with the input it received
and then call the continuation with the result. *)
let try_with #a #labs (f : (unit -> Alg a (Raise::labs))) (g:unit -> Alg a labs)
  : Alg a labs
  = handle_with f
                (fun x -> x)
                (function Raise -> fun _ _ -> g ()
                        | _     -> defh)

let catchE #a #labs (f : unit -> Alg a (Raise::labs)) : Alg (option a) labs =
  handle_with f Some (function Raise -> fun _ _ -> None
                                   | _     -> defh)

(* Repeating the examples above *)
let test_try_with #labs (f : unit -> Alg int [Raise; Write]) : Alg int [Write] =
  let g () : Alg int [] = 42 in
  try_with f g
let test_try_with2 (f : unit -> Alg int [Raise; Write]) : Alg int [Raise; Write] =
  let g () : Alg int [] = 42 in
  try_with f g
[@@expect_failure [19]]
let test_try_with3 (f : unit -> Alg int [Raise; Write]) : Alg int [Write] =
  let g () : Alg int [Raise] = raise (Failure "hmm") in
  try_with f g

(***** The payoff is best seen with handling state *****)

(* Explcitly catching state *)
let rec __catchST0 #a #labs (t1 : tree a (Read::Write::labs)) (s0:state) : tree (a & int) labs =
  match t1 with
  | Return v -> Return (v, s0)
  | Op Write s k -> WF.axiom1 k (); __catchST0 (k ()) s
  | Op Read  _ k -> WF.axiom1 k s0; __catchST0 (k s0) s0
  | Op act i k ->
     (* default case *)
     let k' o : tree (a & int) labs =
       WF.axiom1 k o;
       __catchST0 #a #labs (k o) s0
     in
     Op act i k'

(* An alternative: handling Read/Write into the state monad. The handler
is basically interpreting [Read () k] as [\s -> k s s] and similarly for
Write. Note the stacking of effects: we return a labs-tree that
contains a function which returns a labs-tree. *)
let __catchST1_aux #a #labs (f : tree a (Read::Write::labs))
  : tree (state -> tree (a & state) labs) labs
  = handle_tree #_ #(state -> tree (a & state) labs)
                f
                (fun x ->   Return (fun s0 -> Return (x, s0)))
                (function Read  -> fun _ k -> Return (fun s -> bind _ _ (k s)  (fun f -> f s))
                        | Write -> fun s k -> Return (fun _ -> bind _ _ (k ()) (fun f -> f s))
                        | act   -> fun i k -> Op act i k)

(* Since tree is a monad, however, we can apply the internal function
join the two layers via the multiplication, and recover a more sane
shape. *)
let __catchST1 #a #labs (f : tree a (Read::Write::labs)) (s0:state)
  : tree (a & state) labs
  = bind _ _ (__catchST1_aux f) (fun f -> f s0)
    // = join (fmap (fun f -> f s0) (__catchST1_aux f))

(* Reflecting it into the effect *)
let _catchST #a #labs
  (f : unit -> Alg a (Read::Write::labs))
  (s0 : state)
  : Alg (a & state) labs
  = Alg?.reflect (__catchST1 (reify (f ())) s0)

(* Instead of that cumbersome encoding with the explicitly monadic
handler, we can leverage handle_with and it in direct style. The version
below is essentially the same, but without any need to write binds,
returns, and Op nodes. Note how the layering of the effects is seamlessly
handled except for the need of a small annotation. To apply the handled
stacked computation to the initial state, there is no bind or fmap+join,
just application to s0. *)
let catchST #a #labs (f: unit -> Alg a (Read::Write::labs)) (s0:state)
  : Alg (a & state) labs
  = handle_with #_ #(state -> Alg _ labs) #_ #labs
                f (fun x s -> (x, s))
                  (function Read  -> fun _ k s -> k s s
                          | Write -> fun s k _ -> k () s
                          | _     -> defh) s0

(* Of course, we can also fully run computations into pure functions if
no labels remain *)
let runST #a
  (f : unit -> Alg a (Read::Write::[]))
  : state -> a & state
  = fun s0 -> run (fun () -> catchST f s0)

(* We could also handle it directly if no labels remain, without
providing a default case. F* can prove the match is complete. Note the
minimal superficial differences to catchST. *)
let runST2 #a #labs (f: unit -> Alg a (Read::Write::[])) (s0:state)
  : Alg (a & state) []
  = handle_with #_ #(state -> Alg _ []) #_ #[]
                f (fun x s -> (x, s))
                  (function Read  -> fun _ k s -> k s s
                          | Write -> fun s k _ -> k () s) s0

(* We can interpret state+exceptions as monadic computations in the two usual ways: *)

let run_stexn #a (f : unit -> Alg a [Write; Raise; Read]) (s_0:state) : option (a & state) =
  run (fun () -> catchE (fun () -> catchST f s_0))

let run_exnst #a (f : unit -> Alg a [Write; Raise; Read]) (s_0:state) : option a & state =
  run (fun () -> catchST (fun () -> catchE f) s_0)

(***** There are many other ways in which to program with
handlers, we show a few in what follows. *)

(* Unary read handler which just provides s0 *)
let read_handler (#b:Type)
                 (#labs:ops)
                 (s0:state)
  : handler_op Read b labs
  = fun _ k -> k s0

(* Handling only Read *)
let handle_read (#a:Type)
                (#labs:ops)
                (f : unit -> Alg a (Read::labs))
                (h : handler_op Read a labs)
 : Alg a labs
 = handle_with f (fun x -> x) (function Read -> h
                                   | _ -> defh)

(* A handler for write which handles Reads in the continuation with the
state at hand. Note that `k` is automatically subcomped to ignore a
label. *)
let write_handler (#a:Type)
                  (#labs:ops)
  : handler_op Write a labs
  = fun s k -> handle_read k (read_handler s)

(* Handling writes with the handler above *)
let handle_write (#a:Type)
                 (#labs:ops)
                 (f : unit -> Alg a (Write::labs))
   : Alg a labs
   = handle_with f (fun x -> x)
                   (function Write -> write_handler
                           | _ -> defh)

(* Handling state by 1) handling writes and all the reads
under them via the write handler above 2) handling the initial
Reads. *)
let handle_st (a:Type)
              (labs: ops)
              (f : unit -> Alg a (Write::Read::labs))
              (s0:state)
   : Alg a labs
   = handle_read (fun () -> handle_write f) (fun _ k -> k s0)

(* Widening the domain of a handler by leaving some operations in labs0)
(untouched. Requires being able to compare labels. *)
let widen_handler (#b:_) (#labs0 #labs1:_)
                  (h:handler labs0 b labs1)
  : handler (labs0@labs1) b labs1
  = fun op ->
      (* This relies on decidable equality of operation labels,
       * or at least on being able to decide whether `op` is in `labs0`
       * or not. Since currently they are an `eqtype`, `mem` will do it. *)
      mem_memP op labs0; // "mem decides memP"
      if op `mem` labs0
       then h op
       else defh

(* Partial handling *)
let handle_sub (#a #b:_) (#labs0 #labs1:_)
               (f : unit -> Alg a (labs0@labs1))
               (v : a -> Alg b labs1)
               (h : handler labs0 b labs1)
  : Alg b labs1
  = handle_with f v (widen_handler h)

let widen_handler_1 (#b:_) (#o:op) (#labs1:_)
                       (h:handler_op o b labs1)
  : handler (o::labs1) b labs1
  = widen_handler #_ #[o] (fun _ -> h)

let handle_one (#a:_) (#o:op) (#labs1:_)
               ($f : unit -> Alg a (o::labs1))
               (h : handler_op o a labs1)
  : Alg a labs1
  = handle_with f (fun x -> x) (widen_handler_1 h)

let append_single (a:Type) (x:a) (l:list a)
  : Lemma (x::l == [x]@l)
          [SMTPat (x::l)]
  = ()
  
let handle_raise #a #labs (f : unit -> Alg a (Raise::labs)) (g : unit -> Alg a labs)
  : Alg a labs
  = handle_one f (fun _ _ -> g ())
   
let handle_read' #a #labs (f : unit -> Alg a (Read::labs)) (s:state)
  : Alg a labs
  = handle_one f (fun _ k -> k s)
   
let handle_write' #a #labs (f : unit -> Alg a (Write::labs))
  : Alg a labs
  = handle_one f (fun s k -> handle_read' k s)

let handle_return #a (x:a)
  : Alg (option a & state) [Write; Read]
  = (Some x, get ())

let handler_raise #a
  : handler [Raise; Write; Read] (option a & state) [Write; Read]
  = function
    | Raise -> (fun i k -> (None, get ()))
    | _ -> defh

let handler_raise_write #a
  : handler [Raise; Write] (option a & state) [Write; Read]
  = function
    | Raise -> (fun i k -> (None, get ()))
    | Write -> (fun i k -> handle_write' k)

(* Running by handling one operation at a time *)
let run_tree #a (f : unit -> Alg a [Raise; Write; Read]) (s0:state)
  : option a & state
  = run (fun () ->
     handle_read' (fun () ->
      handle_write' (fun () ->
       handle_with f handle_return handler_raise)) s0)

(* Running state+exceptions *)
let runSTE #a (f: unit -> Alg a [Raise; Write; Read]) (s0:state) : Alg (option a & state) [] =
  handle_with #_ #(state -> Alg (option a & state) []) #[Raise; Write; Read] #[]
               f (fun x s -> (Some x, s))
                 (function Read  -> fun _ k s -> k s s
                         | Write -> fun s k _ -> k () s
                         | Raise -> fun e k s -> (None, s)) s0

(* And into pure *)
let runSTE_pure #a (f: unit -> Alg a [Raise; Write; Read]) (s0:state) : option a & state =
  run (fun () -> runSTE f s0)


(*** Interps into other effects *)

let interp_pure_tree #a (t : tree a []) : Tot a =
  match t with
  | Return x -> x

let interp_pure #a (f : unit -> Alg a []) : Tot a = interp_pure_tree (reify (f ()))

let rec interp_rd_tree #a (t : tree a [Read]) (s:state) : Tot a =
  match t with
  | Return x -> x
  | Op Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rd_tree (k s) s

let interp_rd #a (f : unit -> Alg a [Read]) (s:state) : Tot a = interp_rd_tree (reify (f ())) s

let rec interp_rdwr_tree #a (t : tree a [Read; Write]) (s:state) : Tot (a & state) =
  match t with
  | Return x -> (x, s)
  | Op Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rdwr_tree (k s) s
  | Op Write s k ->
    FStar.WellFounded.axiom1 k ();
    interp_rdwr_tree (k ()) s

let interp_rdwr #a (f : unit -> Alg a [Read; Write]) (s:state) : Tot (a & state) = interp_rdwr_tree (reify (f ())) s

let rec interp_read_raise_tree #a (t : tree a [Read; Raise]) (s:state) : either exn a =
  match t with
  | Return x -> Inr x
  | Op Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_read_raise_tree (k s) s
  | Op Raise e k ->
    Inl e

let interp_read_raise_exn #a (f : unit -> Alg a [Read; Raise]) (s:state) : either exn a =
  interp_read_raise_tree (reify (f ())) s

let rec interp_all_tree #a (t : tree a [Read; Write; Raise]) (s:state) : Tot (option a & state) =
  match t with
  | Return x -> (Some x, s)
  | Op Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_all_tree (k s) s
  | Op Write s k ->
    FStar.WellFounded.axiom1 k ();
    interp_all_tree (k ()) s
  | Op Raise e k ->
    (None, s)

let interp_all #a (f : unit -> Alg a [Read; Write; Raise]) (s:state) : Tot (option a & state) = interp_all_tree (reify (f ())) s

//let action_input (a:action 'i 'o) = 'i
//let action_output (a:action 'i 'o) = 'o
//
//let handler_ty (a:action _ _) (b:Type) (labs:list eff_label) =
//    action_input a ->
//    (action_output a -> tree b labs) -> tree b labs
//
//let dpi31 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : a =
//  let (| x, y, z |) = t in x
//
//let dpi32 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : b (dpi31 t) =
//  let (| x, y, z |) = t in y
//
//let dpi33 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : c (dpi31 t) (dpi32 t) =
//  let (| x, y, z |) = t in z

  //handler_ty (dpi33 (action_of l)) b labs
  //F* complains this is not a function
  //let (| _, _, a |) = action_of l in
  //handler_ty a b labs




(*** Other ways to define handlers *)

(* A generic handler for a (single) label l. Anyway a special case of
handle_tree. *)
val handle (#a #b:_) (#labs:_) (o:op)
           (f:tree a (o::labs))
           (h:handler_tree_op o b labs)
           (v: a -> tree b labs)
           : tree b labs
let rec handle #a #b #labs l f h v =
  match f with
  | Return x -> v x
  | Op act i k ->
    if act = l
    then h i (fun o -> WF.axiom1 k o; handle l (k o) h v)
    else begin
      let k' o : tree b labs =
         WF.axiom1 k o;
         handle l (k o) h v
      in
      Op act i k'
    end

(* Easy enough to handle 2 labels at once. Again a special case of
handle_tree too. *)
val handle2 (#a #b:_) (#labs:_) (l1 l2 : op)
           (f:tree a (l1::l2::labs))
           (h1:handler_tree_op l1 b labs)
           (h2:handler_tree_op l2 b labs)
           (v : a -> tree b labs)
           : tree b labs
let rec handle2 #a #b #labs l1 l2 f h1 h2 v =
  match f with
  | Return x -> v x
  | Op act i k ->
    if act = l1
    then h1 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else if act = l2
    then h2 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else begin
      let k' o : tree b labs =
         WF.axiom1 k o;
         handle2 l1 l2 (k o) h1 h2 v
      in
      Op act i k'
    end

let catch0' #a #labs (t1 : tree a (Raise::labs))
                     (t2 : tree a labs)
  : tree a labs
  = handle Raise t1 (fun i k -> t2) (fun x -> Return x)

let catch0'' #a #labs (t1 : tree a (Raise::labs))
                      (t2 : tree a labs)
  : tree a labs
  = handle_tree t1
                (fun x -> Return x)
                (function Raise -> (fun i k -> t2)
                        | act -> (fun i k -> Op act i k))



(*** Connection to Lattice *)

let baseop = o:op{not (Other? o)}

let trlab : o:baseop -> L.eff_label = function
  | Read  -> L.RD
  | Write  -> L.WR
  | Raise -> L.EXN

let trlab' = function
  | L.RD  -> Read
  | L.WR  -> Write
  | L.EXN -> Raise

let trlabs  = List.Tot.map trlab
let trlabs' = List.Tot.map trlab'

let rec lab_corr (l:baseop) (ls:list baseop)
  : Lemma (l `memP` ls <==> (trlab l) `mem` (trlabs ls))
          [SMTPat (l `memP` ls)] // needed for interp_into_lattice_tree below
  = match ls with
    | [] -> ()
    | l1::ls -> lab_corr l ls

(* Tied to the particular tree of Lattice.fst *)

(* no datatype subtyping *)
let fixup : list baseop -> ops = List.Tot.map #baseop #op (fun x -> x)

let rec fixup_corr (l:baseop) (ls:list baseop)
  : Lemma (l `memP` (fixup ls) <==> l `memP` ls)
          [SMTPat (l `memP` (fixup ls))]
  = match ls with
    | [] -> ()
    | l1::ls -> fixup_corr l ls
    
let rec fixup_no_other (l:op{Other? l}) (ls:list baseop)
  : Lemma (l `memP` (fixup ls) <==> False)
          [SMTPat (l `memP` (fixup ls))]
  = match ls with
    | [] -> ()
    | l1::ls -> fixup_no_other l ls

// This would be a lot nicer if it was done in L.EFF itself,
// but the termination proof fails since it has no logical payload.
let rec interp_into_lattice_tree #a (#labs:list baseop)
  (t : tree a (fixup labs))
  : L.repr a (trlabs labs)
  = match t with
    | Return x -> L.return _ x
    | Op Read i k ->
      L.bind _ _ _ _ (reify (L.get i))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_tree #a #labs (k x))
    | Op Write i k ->
      L.bind _ _ _ _ (reify (L.put i))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_tree #a #labs (k x))
    | Op Raise i k ->
      L.bind _ _ _ _ (reify (L.raise ()))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_tree #a #labs (k x))

let interp_into_lattice #a (#labs:list baseop)
  (f : unit -> Alg a (fixup labs))
  : Lattice.EFF a (trlabs labs)
  = Lattice.EFF?.reflect (interp_into_lattice_tree (reify (f ())))

// This is rather silly: we reflect and then reify. Maybe define interp_into_lattice
// directly?
let interp_full #a (#labs:list baseop)
  (f : unit -> Alg a (fixup labs))
  : Tot (f:(state -> Tot (option a & state)){Lattice.abides f (Lattice.interp (trlabs labs))})
  = reify (interp_into_lattice #a #labs f)


(* Doing it directly. *)

type sem0 (a:Type) : Type = state -> Tot (either exn a & state)

let abides' (f : sem0 'a) (labs:list baseop) : prop =
    (Read  `memP` labs \/ (forall s0 s1. fst (f s0) == fst (f s1)))
  /\ (Write `memP` labs \/ (forall s0. snd (f s0) == s0))
  /\ (Raise `memP` labs \/ (forall s0. Inr? (fst (f s0))))

type sem (a:Type) (labs : list baseop) = r:(sem0 a){abides' r labs}

let rec interp_sem #a (#labs:list baseop) (t : tree a (fixup labs)) : sem a labs =
  match t with
  | Return x -> fun s0 -> (Inr x, s0)
  | Op Read _ k ->
    (* Needs this trick for termination. Trying to call axiom1 within
     * `r` messes up the refinement about Read. *)
    let k : (s:state -> (r:(tree a (fixup labs)){r << k})) = fun s -> WF.axiom1 k s; k s in
    let r : sem a labs = fun s0 -> interp_sem #a #labs (k s0) s0 in
    r
  | Op Write s k ->
    WF.axiom1 k ();
    fun s0 -> interp_sem #a #labs (k ()) s
  | Op Raise e k -> fun s0 -> (Inl e, s0)

(* Way back: from the pure ALG into the free one, necessarilly giving
a fully normalized tree *)

let interp_from_lattice_tree #a #labs
  (t : L.repr a labs)
  : tree a [Read; Raise; Write] // conservative
  = Op Read () (fun s0 ->
     let (r, s1) = t s0 in
     match r with
     | Some x -> Op Write s1 (fun _ -> Return x)
     | None   -> Op Write s1 (fun _ -> Op Raise (Failure "") (fun x -> match x with))) // empty match
