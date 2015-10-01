(*--build-config
  options:--verify_module C_Trans;
  variables:SST=../low-level;
  other-files:classical.fst ext.fst set.fsi set.fst seq.fsi seq.fst heap.fst st.fst all.fst seqproperties.fst list.fst listTot.fst $SST/stack.fst $SST/listset.fst ghost.fst $SST/located.fst $SST/lref.fst $SST/regions.fst $SST/rst.fst lsarray.fst
  --*)


module C_Trans

open FStar.Seq

type ptr (a:Type) = | Ptr: v:a -> ptr a

type list (a:Type) =
  | Nil
  | Cons: hd:a -> tl:list a -> list a

type pair (a:Type) (b:Type) = | Pair: fst:a -> snd:b -> pair a b

type option (a:Type) =
  | None
  | Some : v:a -> option a

(* Array with immutable length (check how to works out) *)
//type array (a:Type) = | Array : l:nat -> c:ref (s:seq a{Seq.length s = l})  -> array a

(* Test type, not polymorphic *)
type t =
  | A
  | B
  | C: x:int -> t
  | D: x:int -> y:char -> t

val hd: #a:Type -> l:list a{ is_Cons l } -> Tot a
let hd l =
  Cons.hd l


val test_hd: int -> Tot int
let test_hd x =
  let l = Cons x Nil in
  let l2 = Cons 1 l in
  let res = hd l2 in
  res

val test_hd_1: unit -> Tot int
  let test_hd_1 () =
    let x = 2 in
    let l = Cons x Nil in
    let l3 = Cons 1 l in
    let res = hd l3 in
    res

val test_hd_2: #a:Type -> x:a -> y:a -> Tot a
let test_hd_2 x y =
  let l = Cons x (Cons y Nil) in
  let res = hd l in
  res

val test_pair_1: #a:Type -> #b:Type -> x:a -> y:b -> Tot (pair a b)
let test_pair_1 x y =
  let res = Pair x y in
  res

val test_pair_2: #a:Type -> x:char -> y:a -> Tot (pair char a)
let test_pair_2 x y =
  let res = Pair x y in
  res

val test_pair_3: x:char -> y:int -> Tot (pair char int)
let test_pair_3 x y =
  let res = Pair x y in
  res

val global_test: x:char -> y:int -> Tot int
let global_test x y =
  let z = x in
  let a1 = test_pair_1 x z in
  let a2 = test_pair_1 x y in
  let a3 = test_pair_2 x y in
  let a4 = test_pair_3 x y in
  let res = y in
  res

(*
let rec double x = 2 * x
and triple x = 3 * x
and lalala x = x
*)

val trivial_lemma: 
  x:int -> y:int -> 
  Lemma
    (requires (x >= 0 /\ y >= 0))
    (ensures (x + y >= 0))
let trivial_lemma x y = ()

// Computationally irrelevant, should be erased
val do_nothing: int -> int -> Tot unit
let do_nothing x y =
  let a = x in
  let b = y in
  let c = a + b in
  let res = () in
  res

// GTot, should be erased
val double_gtot: int -> GTot int
let double_gtot x = 2 * x

type opt_list (a:Type) = option (ref a)
and _opt_list (a:Type) = a * opt_list a
