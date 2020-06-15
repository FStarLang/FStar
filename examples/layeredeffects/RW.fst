module RW

module H = FStar.Heap
open FStar.Tactics
open FStar.Universe
open FStar.ST

type idx =
 | R
 //| W
 | RW

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let m (a:Type u#aa) (i:idx) : Type0 =
  match i with
  | R  -> (unit -> ST a (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1)))
  //| W  -> unit -> ST a (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
  | RW -> unit -> ST a (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))

let return_r  #a (x:a) : m a R  = fun () -> x
let return_rw #a (x:a) : m a RW = fun () -> x

let reveal_r #a (f : m a R) : (unit -> ST a (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))) =
  f
  
let reveal_rw #a (f : m a RW) : (unit -> ST a (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))) =
  f
  
let pack_r #a (f : unit -> ST a (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))) : m a R =
  f
  
let pack_rw #a (f : (unit -> ST a (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)))) : m a RW =
  f

let return (a:Type) (x:a) (i:idx) : m a i =
  match i with
  | R  -> return_r x
  | RW -> return_rw x

let bind_r #a #b ($c : m a R) ($f : a -> m b R) : m b R = fun () -> f (c ()) ()
let bind_rw #a #b ($c : m a RW) ($f : a -> m b RW) : m b RW = fun () -> f (c ()) ()

let bind (a b : Type) (i:idx) (c : m a i) (f : a -> m b i) : m b i =
  match i with
  | R  -> coerce (bind_r #a #b c f)
  | RW -> coerce (bind_rw #a #b c f)

// Already somewhat usable
let rec r_map #i #a #b (f : a -> m b i) (xs : list a) : m (list b) i =
  match xs with
  | [] -> return _ [] _
  | x::xs ->
    bind _ _ _ (f x) (fun y ->
    bind _ _ _ (r_map f xs) (fun ys ->
    return _ (y::ys) _))

// cannot make this prop
val flows : idx -> idx -> Type0
let flows i1 i2 =
  match i1, i2 with
  | RW, R -> False
  | _, _ -> True

// fails with ref
//val join : i1:idx -> i2:idx -> r:idx{flows i1 r /\ flows i2 r}
val join : i1:idx -> i2:idx -> idx
let join i1 i2 =
  match i1, i2 with
  | R, R -> R
  | _, _ -> RW

let subcomp (a:Type) (i1 i2 :idx) (f : m a i1) : Pure (m a i2)
                                                      (requires (flows i1 i2))
                                                      (ensures (fun _ -> True))
  = match i1, i2 with
    | R, R -> coerce f
    | RW, RW -> coerce f
    | R, RW -> 
      let f' () : ST a (fun _ -> True) (fun _ _ _ -> True) = reveal_r f () in
      f'


#set-options "--debug RW --debug_level SMTQuery"

// GM: I'm surprised this works, I thought we had the req that
//
//    p ==> if_then_else _ _ _ f1 f2 = (typeof f1)
//
// but that's not true since the join can raise the index... unless the _ are solved to
// the same index? is that ok?
let if_then_else (a:Type) (i1 i2:idx) (f : m a i1) (g : m a i2) (p : Type0) : Type =
  m a (join i1 i2)

reifiable
reflectable
layered_effect {
  RWI : a:Type -> idx -> Effect
  with
  repr         = m;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let lift_pure_rwi (a:Type) (wp : pure_wp a) (i : idx)
                  (f : unit -> PURE a wp)
                 : Pure (m a i)
                        (requires (wp (fun _ -> True) /\ (forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2)))
                        (ensures (fun _ -> True))
 =
 match i with
 | R ->
   let f' () : ST a (fun _ -> True) (fun h0 _ h1 -> h0 == h1) = f () in
   f'
 | RW ->
   let f' () : ST a (fun _ -> True) (fun h0 _ h1 -> True) = f () in
   f'

sub_effect PURE ~> RWI = lift_pure_rwi

// cannot resolve an index
[@@expect_failure]
let rec map #a #b (#i:idx) (f : a -> RWI b i) (xs : list a) : RWI (list b) i =
  match xs with
  | [] -> []
  | x::xs -> (f x)::(map #_ #_ #i f xs)

let app #a #b #i (f : a -> RWI b i) (x : a) : RWI b i = f x

// also can't resolve an index
[@@expect_failure]
let rec appn #a #i (n:nat) (f : a -> RWI a i) (x : a) : RWI a i =
  match n with 
  | 0 -> x
  | _ -> begin
    assume (n>0);
    appn (n-1) f (f x)
  end

// explodes
//[@@expect_failure]
//let test #a #i (n:int) : GTD nat i =
//  let r = app abs n in
//  r

let labs0 #i (n:int) : RWI int i =
  if n < 0
  then -n
  else n
  
let labs #i (n:int) : RWI nat i =
  if n < 0
  then -n
  else n

[@@expect_failure]
let test #a #i (n:int) : RWI nat i =
  let r = labs0 n in
  assume (r >= 0);
  r

let getr () : RWI H.heap R =
  RWI?.reflect begin
    let f' () : ST H.heap (fun _ -> True) (fun h0 _ h1 -> h0 == h1) = get () in
    pack_r f'
  end

let get (#i:idx) () : RWI H.heap i =
  RWI?.reflect begin
    match i with
    | R ->
      let f' () : ST H.heap (fun _ -> True) (fun h0 _ h1 -> h0 == h1) = get () in
      pack_r f'

    | RW ->
      let f' () : ST H.heap (fun _ -> True) (fun _ _ _ -> True) = get () in
      pack_rw f'
  end
