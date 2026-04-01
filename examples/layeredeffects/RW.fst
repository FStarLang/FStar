module RW

#set-options "--print_effect_args"

open ExampleHeap
open ExampleST

type idx =
 | RO
 | RW
 
val flows : idx -> idx -> Type0
let flows i1 i2 =
  match i1, i2 with
  | RW, RO -> False
  | _, _ -> True

val join : i1:idx -> i2:idx -> idx
let join i1 i2 =
  match i1, i2 with
  | RO, RO -> RO
  | _, _ -> RW

// Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

type st_pre = heap -> Type0
type st_post (a:Type) = a -> heap -> Type0
type st_bpost (a:Type) = heap -> a -> heap -> Type0

unfold
let ro_post #a (post : st_bpost a) : st_bpost a =
  fun h0 x h1 -> post h0 x h1 /\ h1 == h0

let is_ro_post #a (post : st_bpost a) : Type =
  forall h0 x h1. post h0 x h1 ==> h0 == h1

let ro_sanity_check #a (post : st_bpost a) =
  assert (is_ro_post (ro_post post))

let real_post #a (i : idx) (post : st_bpost a)
  : st_bpost a
  = match i with
    | RO -> ro_post post
    | _ -> post

/// The repr is a function into ExST that encodes pre/post/RO-RW index
let m (a:Type u#aa) (i:idx) (pre : st_pre) (post : st_bpost a): Type0 =
  unit -> ExST a (fun p h -> pre h /\ (forall x h1. real_post i post h x h1 ==> p x h1))
  
let return (a:Type) (x:a) : m a RO (fun _ -> True) (fun h0 y h1 -> y == x /\ h1 == h0) =
  fun () -> x

unfold
let bind_pre #a (i1 i2 : idx)
  (pre : st_pre)
  (pre' : a -> st_pre)
  (post : st_bpost a)
  : st_pre
  = let post = real_post i1 post in
    fun h0 -> pre h0 /\ (forall x h1. post h0 x h1 ==> pre' x h1)
    
unfold
let bind_post #a #b (i1 i2 : idx)
  (pre : st_pre)
  (post : st_bpost a)
  (post' : a -> st_bpost b)
  : st_bpost b
  = let post    : st_bpost a = real_post i1 post in
    let post' x : st_bpost b = real_post i2 (post' x) in
    fun h0 y h2 -> pre h0 /\ (exists x h1. post h0 x h1 /\ post' x h1 y h2)

let bind (a b : Type)
  (i:idx) (pre:st_pre) (post:st_bpost a)
  (i':idx)
  (pre':a -> st_pre) (post':a -> st_bpost b)
  (c : m a i pre post)
  (f : (x:a -> m b i' (pre' x) (post' x)))
  : Tot (m b (join i i') (bind_pre i i' pre pre' post) (bind_post i i' pre post post'))
  = fun () -> let x = c () in f x ()

// a test
let rwi_subtype (a b : Type) (inj : a -> b)
  (i:idx)
  (pre:_) (post:st_bpost a)
  (c : m a i pre post)
  : Tot (m b i pre (fun h0 x h1 -> exists x0. x == inj x0 /\ post h0 x0 h1)) =
  bind _ _ _ _ _ _ _ _ c (fun (x:a) -> return _ (inj x))

let pre_leq (pre1 pre2 : st_pre) =
  forall h. pre2 h ==> pre1 h

let post_leq #a (post1 post2 : st_bpost a) =
  forall h0 x h1. post1 h0 x h1 ==> post2 h0 x h1

let subcomp (a:Type) (i1:idx) (pre : st_pre)  (post  : st_bpost a)
  (i2:idx) (pre' : st_pre) (post' : st_bpost a)
  (f : m a i1 pre post)
  : Pure (m a i2 pre' post')
         (requires (flows i1 i2 /\ pre_leq pre pre' /\ post_leq post post'))
         (ensures (fun _ -> True))
  = fun () -> f ()

unfold
let ite (p q r : Type0) = (p ==> q) /\ (~p ==> r)

let if_then_else
  (a : Type) (i1:idx) 
  (pre1:st_pre) 
  (post1 : st_bpost a)
  (i2 : idx)
  (pre2 : st_pre)
  (post2 : st_bpost a)
  (f : m a i1 pre1 post1) (g : m a i2 pre2 post2)
  (p : bool)
  : Type
  = m a (join i1 i2)
        (fun h0 -> ite p (pre1 h0) (pre2 h0))
        (fun h0 x h1 -> ite p (post1 h0 x h1) (post2 h0 x h1))

reifiable
reflectable
effect {
  RWI (a:Type) (i:idx) (_:st_pre) (_:st_bpost a)
  with {repr         = m;
        return       = return;
        bind         = bind;
        subcomp      = subcomp;
        if_then_else = if_then_else}
}

unfold
let sp #a (wp : pure_wp a) : pure_post a =
  fun x -> ~ (wp (fun y -> ~(x == y)))

let lift_pure_rwi
 (a:Type)
 (wp : pure_wp a)
 (f :unit -> PURE a wp)
 : m a RO (fun _ -> wp (fun _ -> True)) (fun h0 x h1 -> sp wp x /\ h1 == h0)
 = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
   fun () -> f ()
 
sub_effect PURE ~> RWI = lift_pure_rwi

let test_rrr #pre #post (b:bool) (f : unit -> RWI int RO pre post) (g : unit -> RWI int RO pre post) : RWI int RO pre post = if b then f () else g ()

let test_rrw #pre #post (b:bool) (f : unit -> RWI int RO pre post) (g : unit -> RWI int RO pre post) : RWI int RW pre post = if b then f () else g ()

[@@expect_failure]
let test_rwr #pre #post (b:bool) (f : unit -> RWI int RO pre post) (g : unit -> RWI int RW pre post) : RWI int RO pre post = if b then f () else g ()

let test_rww #pre #post (b:bool) (f : unit -> RWI int RO pre post) (g : unit -> RWI int RW pre post) : RWI int RW pre post = if b then f () else g ()

[@@expect_failure]
let test_wrr #pre #post (b:bool) (f : unit -> RWI int RW pre post) (g : unit -> RWI int RO pre post) : RWI int RO pre post = if b then f () else g ()

let test_wrw #pre #post (b:bool) (f : unit -> RWI int RW pre post) (g : unit -> RWI int RO pre post) : RWI int RW pre post = if b then f () else g ()

[@@expect_failure]
let test_wwr #pre #post (b:bool) (f : unit -> RWI int RW pre post) (g : unit -> RWI int RW pre post) : RWI int RO pre post = if b then f () else g ()

let test_www #pre #post (b:bool) (f : unit -> RWI int RW pre post) (g : unit -> RWI int RW pre post) : RWI int RW pre post = if b then f () else g ()

let rec map #a #b
 (f : a -> RWI b RO (fun _ -> True) (fun _ _ _ -> True))
 (xs : list a)
 : RWI (list b) RO (fun _ -> True) (fun _ _ _ -> True)
 = match xs with
   | [] -> []
   | x::xs -> (f x)::(map f xs)

let app #a #b #i #pre #post (f : a -> RWI b i pre post) (x : a) : RWI b i pre post = f x

let rec appn #a #i
  (n:nat)
  (f : a -> RWI a i (fun _ -> True) (fun _ _ _ -> True))
  (x : a)
  : RWI a i (fun _ -> True) (fun _ _ _ -> True)
= match n with 
  | 0 -> x
  | _ -> begin
    appn #_ #i (n-1) f (f x)
  end

let labs0 (n:int) : RWI int RO (fun _ -> True) (fun h0 x h1 -> x >= 0 /\ h1 == h0) =
  if n < 0
  then -n
  else n

let labs (n:int) : RWI nat RO (fun _ -> True) (fun h0 _ h1 -> True) =
  if n < 0
  then -n
  else n

let rwi_assert (p:Type0) : RWI unit RO (fun _ -> p) (fun h0 () h1 -> h0 == h1) =
  RWI?.reflect (fun () -> assert p)
  
let rwi_assume (p:Type0) : RWI unit RO (fun _ -> True) (fun h0 () h1 -> h0 == h1 /\ p) =
  RWI?.reflect (fun () -> assume p)

let test_abs0 (n:int) : RWI int RO (fun _ -> True) (fun h0 r h1 -> r >= 0) =
  let r = labs0 n in
  ();
  ();
  r
  
let test_abs0' (n:int) : RWI nat RO (fun _ -> True) (fun h0 _ h1 -> True) =
  let r = labs0 n in
  let r : nat = r in
  r
  
let test_abs (n:int) : RWI nat RO (fun _ -> True) (fun h0 _ h1 -> True) =
  let r = labs n in
  r

let get_indexed (#i:idx) () : RWI heap i (fun _ -> True) (fun h0 x h1 -> x == h0 /\ h1 == h0) =
  RWI?.reflect (fun () -> ExampleST.get ())

let get_r () : RWI heap RO (fun _ -> True) (fun h0 x h1 -> x == h0 /\ h1 == h0) =
  RWI?.reflect (fun () -> ExampleST.get ())

let get = get_r

let test_state_eq_rrr
  (f g : unit -> RWI int RO (fun _ -> True) (fun _ _ _ -> True))
  : RWI int RO (fun _ -> True) (fun _ _ _ -> True)
  =
  let h0 = get () in
  let x = f () in
  let h1 = get () in
  let y = g () in
  let h2 = get () in
  assert (h0 == h1);
  assert (h1 == h2);
  x + y
  
let test_state_eq_rrw
  (f : unit -> RWI int RO (fun _ -> True) (fun _ _ _ -> True))
  (g : unit -> RWI int RO (fun _ -> True) (fun _ _ _ -> True))
  : RWI int RW (fun _ -> True) (fun _ _ _ -> True)
  =
  let h0 = get () in
  let x = f () in
  let h1 = get () in
  let y = g () in
  let h2 = get () in
  assert (h0 == h1);
  assert (h1 == h2);
  x + y

let test_state_eq_rww
  (f : unit -> RWI int RO (fun _ -> True) (fun _ _ _ -> True))
  (g : unit -> RWI int RW (fun _ -> True) (fun _ _ _ -> True))
  : RWI int RW (fun _ -> True) (fun _ _ _ -> True)
  =
  let h0 = get () in
  let x = f () in
  let h1 = get () in
  let y = g () in
  let h2 = get () in
  assert (h0 == h1);
  x + y

let test_state_eq_www
  (f : unit -> RWI int RW (fun _ -> True) (fun _ _ _ -> True))
  (g : unit -> RWI int RW (fun _ -> True) (fun _ _ _ -> True))
  : RWI int RW (fun _ -> True) (fun _ _ _ -> True)
  =
  let h0 = get () in
  let x = f () in
  let h1 = get () in
  let y = g () in
  let h2 = get () in
  x + y


let makero
  #a #pre (#post : _ {is_ro_post post})
  (f : unit -> RWI a RW pre post)
  : RWI a RO pre post
  = RWI?.reflect (fun () -> reify (f ()) ())
