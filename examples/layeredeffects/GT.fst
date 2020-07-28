module GT

open FStar.Tactics
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
  match i with
  | T -> t_return x
  | G -> g_return x
  | D -> d_return x

let t_bind #a #b (c : m a T) (f : a -> m b T) : m b T = fun () -> f (c ()) ()
let g_bind #a #b (c : m a G) (f : a -> m b G) : m b G = fun () -> f (c ()) ()
let d_bind #a #b (c : m a D) (f : a -> m b D) : m b D =
  raise_val (fun () -> downgrade_val (f (downgrade_val c ())) ())

let bind (a b : Type) (i:idx) (c : m a i) (f : a -> m b i) : m b i =
  match i with
  | T -> t_bind #a #b c f
  | D -> coerce (d_bind #a #b c f) // GM: wow... still needs a coerce, how can that be?
  | G -> g_bind #a #b c f

// Already somewhat usable
let rec r_map #i #a #b (f : a -> m b i) (xs : list a) : m (list b) i =
  match xs with
  | [] -> return _ [] _
  | x::xs ->
    bind _ _ _ (f x) (fun y ->
    bind _ _ _ (r_map f xs) (fun ys ->
    return _ (y::ys) _))

let t1_t () : Tot (list int) = r_map #T (fun x -> fun () -> x + 1) [1;2;3;4] ()
let t1_g () : GTot (list int) = r_map #G (fun x -> fun () -> x + 1) [1;2;3;4] ()
let t1_d () : Dv (list int) = downgrade_val (r_map #D (fun x -> raise_val (fun () -> x + 1)) [1;2;3;4]) ()

let subcomp (a:Type) (i:idx) (f : m a i) : m a i = f

let if_then_else (a:Type) (i:idx) (f : m a i) (g : m a i) (b : bool) : Type = m a i

// GM: Would be nice to not have to use all explicit args everywhere,
//     and to get better errors especially when args are out of order,
//     e.g. the [idx] in [return] needs to come after [x], otherwise
//     we get an assertion failure trying to prove [forall (a: Type). idx == a].

[@@allow_informative_binders]
reifiable
reflectable
layered_effect {
  GTD : a:Type -> idx -> Effect
  with
  repr         = m;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let lift_pure_gtd (a:Type) (wp : pure_wp a) (i : idx)
                  (f : eqtype_as_type unit -> PURE a wp)
                 : Pure (m a i)
                        (requires (wp (fun _ -> True) /\ (forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2)))
                        (ensures (fun _ -> True))
 = //f
 // GM: Surprised that this works actually... I expected that I would need to
 //     case analyze [i].
 // GM: ok not anymore
 match i with
 | T -> f
 | G -> f
 | D -> coerce (raise_val (fun () -> f () <: Dv a))

sub_effect PURE ~> GTD = lift_pure_gtd

let rec map #a #b #i (f : a -> GTD b i) (xs : list a) : GTD (list b) i =
  match xs with
  | []   -> []
  | x::xs -> (f x)::(map f xs)

let app #a #b #i (f : a -> GTD b i) (x : a) : GTD b i = f x

// todo: use map/app from tot context and prove that it does what it's meant to do

open FStar.Tactics

[@@expect_failure]
let rec appn #a #i (n:nat) (f : a -> GTD a i) (x : a) : GTD a i =
  match n with
  | 0 -> x
  | _ -> begin
    assume (n>0);
    appn (n-1) f (f x)
  end

[@@expect_failure]
let test #a #i (n:int) : GTD nat i =
  let r = app abs n in
  r

let labs0 #i (n:int) : GTD int i =
  if n < 0
  then -n
  else n

let labs #i (n:int) : GTD nat i =
  if n < 0
  then -n
  else n

// GM: This fails, which I think makes sense since the effect
//     doesn't carry any logical payload, so the assume gets lost?
[@@expect_failure]
let test #a #i (n:int) : GTD nat i =
  let r = labs0 n in
  assume (r >= 0);
  r
