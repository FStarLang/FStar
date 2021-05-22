module Funcs

(* A bunch of tests regarding dependent function types, unfolding,
unification, recursion, and divergence. *)

(* Ignore "recursive but not used in its body" warnings *)
#set-options "--warn_error -328"

let rec f0 = fun (x:nat) -> if x > 0 then f0 (x-1) else 0

(* Some sanity checks about recursion arity (see #1017) *)

let rec dv_0 (x:nat) (y:nat) : Dv nat = dv_0 x y
let rec dv_1 (x:nat) : nat -> Dv nat = fun y -> dv_1 x y

(* Should fail, recursing is happening in `Tot`, but it doesn't
terminate *)
[@@expect_failure [19]]
let rec dv_2 (x:nat) : nat -> Dv nat = dv_2 x

let rec dv_3 (x:nat) : Dv (nat -> Dv nat) = dv_3 x
let rec dv_4 (x:nat) : Dv (nat -> Tot nat) = dv_4 x

(* Examples from issue #1182 *)

type func = nat -> Tot nat

val bug1182_id0 (f:func) : func
let bug1182_id0 (f:func) = f

val bug1182_id1 (f:func) : func
let bug1182_id1 (f:func) = fun n -> f n

val bug1182_id2 (f:func) : func
let rec bug1182_id2 (f:func) = f

val bug1182_id3 (f:func) : func
let rec bug1182_id3 (f:func) = fun n -> f n

type funcfunc = func -> func

val bug1182_id0' : funcfunc
let bug1182_id0' (f:func) = f

val bug1182_id1' : funcfunc
let bug1182_id1' (f:func) = fun n -> f n

val bug1182_id2' : funcfunc
let rec bug1182_id2' (f:func) = f

val bug1182_id3' : funcfunc
let rec bug1182_id3' (f:func) = fun n -> f n

let rec bug1182_id5 f = fun n -> f n

type unOp 'a = 'a -> 'a
type unOp2 'a = unOp 'a -> unOp 'a

val bug1182_twice0 : unOp 'a -> unOp 'a
let bug1182_twice0 f x = f (f x)

val bug1182_twice1 : unOp 'a -> unOp 'a
let rec bug1182_twice1 f x = f (f x)

val bug1182_twice0' : unOp2 'a
let bug1182_twice0' f x = f (f x)

val bug1182_twice1' : unOp2 'a
let rec bug1182_twice1' f x = f (f x)

// Recursion arity 1
val id3 (f:func) : Tot func (decreases f)
let rec id3 f = fun n ->
    f n

// Recursion arity 2
val id4 (f:func) : func
let rec id4 f = fun n ->
    f n

let id x = x

let rec f : unit -> Dv (unit -> Dv unit) =
  fun x ->
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  let r = fun y -> f () () in r
and g : unit -> Dv unit =
  fun () -> f () ()

let rec loop0 (x : int) : int -> Dv int = fun y -> loop0 (x - 1) y

(* This has to fail: the recursing is happening at "arity 1",
but the "Dv" is at "arity 2". *)
[@@expect_failure [19]]
let rec loop (x : int) : Tot (int -> Dv int) = loop (x - 1)

let rec loop_ok (x : int) (y : int): Dv int = loop_ok (x - 1) y

assume val f1 (n : nat) (m : bool) :
  Dv bool

(* Fails as it should, we're stating that l decreases but
it does not. *)
[@@expect_failure [19]]
let rec nest_0 (l : list nat)
  : Tot (n : bool -> Dv bool)
        (decreases l)
  = fun n ->
    match l with
    | [] -> false
    | x :: l' ->
      let r = f1 x n in
      if r then nest_0 l n else r

(* Works when correct *)
let rec nest_1 (l : list nat)
  : Tot (n : bool -> Dv bool)
        (decreases l)
  = fun n ->
    match l with
    | [] -> false
    | x :: l' ->
      let r = f1 x n in
      if r then nest_1 l' n else r

(* Used to explode *)
val list_ref: unit -> u:unit{l_Forall (fun (x:int) -> True)} -> Tot unit
let rec list_ref _ _ = ()

(* Blew up at some point since the implicit of id had
an ill-scoped decreases clause. *)
let test_scope_decreases = id nest_1

open FStar.List.Tot

val concatlemma (#a:Type) (l1 l2 :list a) (x:a) : Lemma (memP x (l1@l2) <==> memP x l1 \/ memP x l2)

let rec concatlemma l1 l2 x =
  match l1 with
  | [] -> ()
  | h::t -> concatlemma t l2 x

val concatmaplemma : (#a:Type) -> (#b:Type) -> l:list a -> (f:(a -> list b)) -> x:b ->
                               Lemma (memP x (concatMap f l) <==> (exists a. memP a l /\ memP x (f a)))
                                     [SMTPat (memP x (concatMap f l))]

let rec concatmaplemma l f x =
  match l with
  | [] -> ()
  | h::t ->
    concatlemma (f h) (concatMap f t) x;
    concatmaplemma t f x
