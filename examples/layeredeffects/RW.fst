module RW

#set-options "--print_effect_args"

module H = FStar.Heap
open FStar.Tactics
open FStar.Universe
open FStar.ST

type idx =
 | RO
 | RW
 
// cannot make this prop
val flows : idx -> idx -> Type0
let flows i1 i2 =
  match i1, i2 with
  | RW, RO -> False
  | _, _ -> True

// fails later if we use this refinement
//val join : i1:idx -> i2:idx -> r:idx{flows i1 r /\ flows i2 r}
val join : i1:idx -> i2:idx -> idx
let join i1 i2 =
  match i1, i2 with
  | RO, RO -> RO
  | _, _ -> RW

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

// unfold
// let rowp #a (wp : st_wp a) : st_wp a =
//   fun p h0 -> wp (fun x h1 -> h0 == h1 ==> p x h1) h0
// 
// let st_monotonic #a (wp : st_wp a) : Type =
//   forall p1 p2 h0. (forall x h1. p1 x h1 ==> p2 x h1) ==> wp p1 h0 ==> wp p2 h0
// 
// let test_ro
//   (#wp:_{st_monotonic wp})
//   (f : unit -> STATE int (rowp wp))
// : ST int (fun h0 -> wp (fun _ _ -> True) h0) (fun _ _ _ -> True)
// = let h0 = get ()in
//   let _ = f () in
//   let h1 = get ()in
//   assert (h0 == h1);
//   42

// this can be seen as a lifting from RO postconditions to RW postconditions
unfold
let ro_post #a (post : H.heap -> st_post a) : H.heap -> st_post a =
  fun h0 x h1 -> post h0 x h1 /\ h1 == h0

let is_ro_post #a (post : H.heap -> st_post a) : Type =
  forall h0 x h1. post h0 x h1 ==> h0 == h1

let st_bpost (a:Type) : Type =
  H.heap -> a -> H.heap -> Type0
  
let ro_sanity_check #a (post : H.heap -> st_post a) =
  assert (is_ro_post (ro_post post))

let real_post #a (i : idx) (post : st_bpost a)
  : st_bpost a
  = match i with
    | RO -> ro_post post
    | _ -> post
  
// GM: Note, postconditions are totally defined, their well-typing cannot
// depend on pre (see issue #57 and the `st_post'` type).
let m (a:Type u#aa) (i:idx) (pre : st_pre) (post : st_bpost a): Type0 =
  unit -> ST a pre (real_post i post)
  
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
  (i i' :idx)
  (pre:_) (post:st_bpost a)
  (pre':_) (post':a -> st_bpost b)
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

let post_leq #a (post1 post2 : H.heap -> st_post a) =
  forall h0 x h1. post1 h0 x h1 ==> post2 h0 x h1

// how is subtyping handled? can I subtype on a?
// note that post is contravariant in a
let subcomp (a:Type) (i1 i2 :idx)
  (pre : st_pre)  (post  : st_bpost a)
  (pre' : st_pre) (post' : st_bpost a)
  (f : m a i1 pre post)
  : Pure (m a i2 pre' post')
         (requires (flows i1 i2 /\ pre_leq pre pre' /\ post_leq post post'))
         (ensures (fun _ -> True))
  = fun () -> f ()
  
let ite (p q r : Type0) = (p ==> q) /\ (~p ==> r)

let if_then_else
  (a : Type) (i1 i2 : idx)
  (pre1 pre2 : st_pre)
  (post1 : st_bpost a)
  (post2 : st_bpost a)
  (f : m a i1 pre1 post1) (g : m a i2 pre2 post2)
  (p : bool)
  : Type
  = m a (join i1 i2)
        (fun h0 -> ite p (pre1 h0) (pre2 h0))
        (fun h0 x h1 -> ite p (post1 h0 x h1) (post2 h0 x h1))

[@@allow_informative_binders]
reifiable
reflectable
layered_effect {
  RWI : a:Type -> i:idx -> st_pre -> st_bpost a  -> Effect
  with
  repr         = m;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

unfold
let pure_monotonic #a (wp : pure_wp a) : Type =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

unfold
let sp #a (wp : pure_wp a) : pure_post a =
  fun x -> ~ (wp (fun y -> ~(x == y)))

let lift_pure_rwi
 (a:Type)
 (wp : pure_wp a)
 (f : eqtype_as_type unit -> PURE a wp)
 // with the index-polymorphic bind above, this has to be in RO,
 // or unification will usually not find the index here
 : Pure (m a RO (fun _ -> wp (fun _ -> True)) (fun h0 x h1 -> sp wp x /\ h1 == h0))
        (requires pure_monotonic wp)
        (ensures (fun _ -> True))
 = fun () -> f ()
 
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

// can't resolve an index, providing it explicitly with #i makes it explode too
// update: actually, putting a dollar sign on f makes it work... why? I can see
// why it helps to find the index but why doesn't it explode too?

(*
 * AR: Could not resolve #i in the recursive call
 *)
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
  // assert p // fails
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
  let r : nat = r in // need this! an ascription won't work!
  r
  
let test_abs (n:int) : RWI nat RO (fun _ -> True) (fun h0 _ h1 -> True) =
  let r = labs n in
  r

// just a test
let get_indexed (#i:idx) () : RWI H.heap i (fun _ -> True) (fun h0 x h1 -> x == h0 /\ h1 == h0) =
  RWI?.reflect (fun () -> ST.get ())

let get_r () : RWI H.heap RO (fun _ -> True) (fun h0 x h1 -> x == h0 /\ h1 == h0) =
  RWI?.reflect (fun () -> ST.get ())

//let get #i = get_indexed #i
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
  //assert (h0 == h1);
  //assert (h1 == h2);
  x + y


let makero
  #a #pre (#post : _ {is_ro_post post})
  (f : unit -> RWI a RW pre post)
  : RWI a RO pre post
  = RWI?.reflect (fun () -> reify (f ()) ())
