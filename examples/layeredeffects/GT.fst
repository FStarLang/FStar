module GT

(* This example used a layered effect indexed by T/G/D.  Effect indices are gone,
   but the useful part remains as a plain type-indexed monad whose
   representation chooses Tot, GTot, or Dv. *)

open FStar.Tactics.V2
open FStar.Universe

type idx =
 | T
 | G
 | D

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let m (a:Type u#aa) (i:idx) : Type u#aa =
  match i with
  | T -> unit -> Tot  a
  | G -> unit -> GTot a
  | D -> raise_t (unit -> Dv a)

let t_return #a (x:a) : m a T = (fun () -> x)
let g_return #a (x:a) : m a G = (fun () -> x)
let d_return #a (x:a) : m a D = raise_val (fun () -> x)

let return (a:Type) (x:a) (i:idx) : m a i =
  match i returns m a i with
  | T -> t_return x
  | G -> g_return x
  | D -> d_return x

let t_bind #a #b (c : m a T) (f : a -> m b T) : m b T = fun () -> f (c ()) ()
let g_bind #a #b (c : m a G) (f : a -> m b G) : m b G = fun () -> f (c ()) ()
let d_bind #a #b (c : m a D) (f : a -> m b D) : m b D =
  raise_val (fun () -> downgrade_val (f (downgrade_val c ())) ())

let bind (a b : Type) (i:idx) (c : m a i) (f : a -> m b i) : m b i =
  match i returns m b i with
  | T -> t_bind #a #b c f
  | D -> d_bind #a #b (coerce c) f // GM: wow... still needs a coerce, how can that be?
  | G -> g_bind #a #b c f

let (let!) (#a #b : Type) (#i:idx) (c : m a i) (f : a -> m b i) : m b i =
  bind a b i c f

// Already somewhat usable
let rec r_map #i #a #b (f : a -> m b i) (xs : list a) : m (list b) i =
  match xs with
  | [] -> return _ [] _
  | x::xs ->
    let! y = f x in
    let! ys = r_map f xs in
    return _ (y::ys) _

let t1_t () : Tot (list int) = r_map #T (fun x -> fun () -> x + 1) [1;2;3;4] ()
let t1_g () : GTot (list int) = r_map #G (fun x -> fun () -> x + 1) [1;2;3;4] ()
let t1_d () : Dv (list int) = downgrade_val (r_map #D (fun x -> raise_val (fun () -> x + 1)) [1;2;3;4]) ()

// GM: Would be nice to not have to use all explicit args everywhere,
//     and to get better errors especially when args are out of order,
//     e.g. the [idx] in [return] needs to come after [x], otherwise
//     we get an assertion failure trying to prove [forall (a: Type). idx == a].

let rec map #a #b #i (f : a -> m b i) (xs : list a) : m (list b) i =
  match xs with
  | []   -> return _ [] _
  | x::xs ->
    let! y = f x in
    let! ys = map f xs in
    return _ (y::ys) _

let app #a #b #i (f : a -> m b i) (x : a) : m b i = f x

// todo: use map/app from tot context and prove that it does what it's meant to do

let rec appn #a #i (n:nat) (f : a -> m a i) (x : a) : m a i =
  match n with
  | 0 -> return _ x _
  | _ -> begin
    let! y = f x in
    appn (n-1) f y
  end

[@@expect_failure]
let test_abs_negative #a #i (n:int) : m nat i =
  let! r = app (fun x -> return _ (abs x) _) n in
  return _ r _

let labs0 #i (n:int) : m int i =
  return _ (if n < 0 then -n else n) _

let labs #i (n:int) : m nat i =
  return _ (if n < 0 then -n else n) _

let test_abs #a #i (n:int) : m nat i =
  let! r = labs0 #i n in
  assume (r >= 0);
  return _ (r <: nat) _
