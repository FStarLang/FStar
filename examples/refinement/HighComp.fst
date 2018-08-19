module HighComp

open FStar.Classical

module U32 = FStar.UInt32


type mint = U32.t
type state = mint * mint

// High-level specs live in [comp]
let comp a = state -> M (a * state)

type hwp 'a = state -> ('a * state -> Type) -> Type  // x:hwp a { monotonic x }

// [comp] type with wp
type comp_wp 'a (wp : hwp 'a) = s0:state -> PURE ('a * state) (wp s0)

type comp_wp' 'a (wp : hwp 'a) = s0:state -> PURE ('a * state) (wp s0)

// [comp] type with pre- and postconditions
let comp_p (a:Type) (pre : state -> Type) (post : state -> a * state -> Type) : GTot Type  =
    s0:state -> Pure (a * state) (pre s0) (post s0)

// DSL combinators without WP indexing

val hreturn : (a:Type) -> a -> comp a
let hreturn (a:Type) (x : a) = fun s -> (x, s)

val hbind : (a:Type) -> (b:Type) -> comp a -> (a -> comp b) -> comp b
let hbind (a:Type) (b:Type) (m : comp a) (f : a -> comp b) =
    fun s -> let (x, s1) = m s in f x s1

val hread : i:int -> comp mint
let hread (i:int) : comp mint =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)

val hwrite : i:int -> v:mint -> comp unit
let hwrite (i:int) (v:mint) : comp unit =
    fun s -> if i = 0 then ((), (v, snd s))
          else ((), (fst s, v))



// Effect definition

// NOTE : ommiting type annotations from hread and hwrite defs
// makes the effect definition fail

total reifiable reflectable new_effect {
      HIGH : a:Type -> Effect
      with repr  = comp
      ; bind     = hbind
      ; return   = hreturn
      ; get      = hread
      ; put      = hwrite
}


// WPs

let monotonic #a (wp:HIGH?.wp a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2} (forall x. p1 x ==> p2 x) ==> wp s p1 ==> wp s p2

unfold
let return_wp (x : 'a) : hwp 'a =  fun s0 post -> post (x, s0)

//Re-define bind_elab with implicit parameters for easier use
let bind_elab #a #b #f_w ($f:_) #g_w ($g:_) = HIGH?.bind_elab a b f_w f g_w g
assume val range0: range

let bind_wp = HIGH?.bind_wp range0

let read_wp (i:nat) : hwp mint = fun s0 post -> post (hread i s0)

let write_wp (i:nat) (v:mint) : hwp unit = fun s0 post -> post (hwrite i v s0)

(** Monotonicity of WPs  *)

let return_wp_mon (#a:Type) (x : a) : Lemma (monotonic (return_wp x)) =
  let p (p1 : a * state -> Type) (p2 : a * state -> Type) (s : state) 
        (h: squash (forall y. p1 y ==> p2 y)) : GTot (squash (return_wp x s p1 ==> return_wp x s p2)) = 
        ()
  in
  let p' p1 p2 s : Lemma ((forall y. p1 y ==> p2 y) ==> (return_wp x s p1 ==> return_wp x s p2)) = 
    arrow_to_impl (p p1 p2 s)
  in
  forall_intro_3 p'

let write_wp_mon (i:nat) (v:mint) : Lemma (monotonic (write_wp i v)) = 
  let p (p1 : unit * state -> Type) (p2 : unit * state -> Type) (s : state) 
        (h: squash (forall y. p1 y ==> p2 y)) : GTot (squash (write_wp i v s p1 ==> write_wp i v s p2)) = 
        ()
  in
  let p' p1 p2 s : Lemma ((forall y. p1 y ==> p2 y) ==> (write_wp i v s p1 ==> write_wp i v s p2)) = 
    arrow_to_impl (p p1 p2 s)
  in
  forall_intro_3 p'


let read_wp_mon (i:nat) : Lemma (monotonic (read_wp i)) =
  let p (p1 : mint * state -> Type) (p2 : mint * state -> Type) (s : state) 
        (h: squash (forall y. p1 y ==> p2 y)) : GTot (squash (read_wp i s p1 ==> read_wp i s p2)) = 
        ()
  in
  let p' p1 p2 s : Lemma ((forall y. p1 y ==> p2 y) ==> (read_wp i s p1 ==> read_wp i s p2)) = 
    arrow_to_impl (p p1 p2 s)
  in
  forall_intro_3 p'


let bind_wp_mon #a #b (wp1 : hwp a) (wp2 : a -> hwp b) :
    Lemma (requires (monotonic wp1 /\ (forall a. monotonic (wp2 a))))
          (ensures (monotonic (bind_wp a b wp1 wp2))) = admit ()

// Pre and postconditions

unfold
let trivial_pre = fun s0 -> True

unfold
let return_post (#a : Type) (x : a) = fun s0 r -> let (x1, s1) = r in x1 == x /\ s0 == s1

unfold
let bind_pre (#a : Type) (x : a) = fun s0 r -> let (x1, s1) = r in x1 == x /\ s0 == s1

unfold
let bind_post (#a : Type) (x : a) = fun s0 r -> let (x1, s1) = r in x1 == x /\ s0 == s1

// High-level DSL with WP indexing

let return_elab (#a:Type) (x : a) = HIGH?.return_elab a x

// let hbind' (#a:Type) (#b:Type) (#wp1:hwp a) (#wp2:a -> hwp b)
//   (m : comp_wp a wp1) (f : (x:a) -> comp_wp b (wp2 x)) :
//   comp_wp b (bind_wp wp1 wp2) =
//   fun s -> admit ();
//         let (a, s1) = m s in f a s1

val hread' : i:nat -> comp_wp mint (read_wp i)
let hread' (i:nat) : comp_wp mint (read_wp i) =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)

val hwrite' : i:nat -> v:mint -> comp_wp unit (write_wp i v)
let hwrite' (i:nat) (v:mint) : comp_wp unit (write_wp i v) =
    fun s -> if i = 0 then ((), (v, snd s))
          else ((), (fst s, v))




// Commutation
val h_eq : (#a:Type) -> (wp1:hwp a) -> (wp2:hwp a) -> (comp_wp a wp1) -> (comp_wp a wp2) -> GTot Type0
let h_eq #a wp1 wp2 c1 c2 =
    monotonic wp1 /\
    monotonic wp2 /\
    (forall s0. wp1 s0 (fun _ -> True) <==> wp2 s0 (fun _ -> True)) /\
    (forall s0. wp1 s0 (fun _ -> True) ==> wp2 s0 (fun _ -> True) /\ c1 s0 == c2 s0)

// Equivalence with reified computations

// let hreturn_eq (#a:Type) (x : a) :
//   Lemma (h_eq (return_wp x) (return_wp x) (hreturn' x) (reify (HIGH?.return x))) = ()
// ERROR : HighComp.__proj__HIGH__item__return not found

let hwrite_eq (#a:Type) (i:nat) (v:mint) :
   Lemma (h_eq (write_wp i v) (write_wp i v) (hwrite' i v) (reify (HIGH?.put i v))) = ()

let hread_eq (#a:Type) (i:nat) :
   Lemma (h_eq (read_wp i) (read_wp i) (hread' i) (reify (HIGH?.get i))) = ()


open FStar.Tactics

let h_thunk a wp = unit -> HIGH a wp

let reify_bind_commutes
          (#a #b : _)
          (#wp1 : _) ($c1:h_thunk a wp1)
          (#wp2 : _) ($c2: (x:a -> h_thunk b (wp2 x)))
          (s0:_{(monotonic wp1 /\
                (forall x. monotonic (wp2 x)) /\
                bind_wp _ _ wp1 wp2 s0 (fun _ -> True))})
     = reify (let x = c1 () in c2 x ()) s0 ==
       bind_elab (reify (c1 ()))
                 (fun x -> reify (c2 x ())) s0

let test (i:nat) (v:mint) (s0:_) =
    assert (reify (let _ = HIGH?.put i v in
                   HIGH?.put i v) s0 ==
            bind_elab (reify (HIGH?.put i v))
                      (fun _ -> reify (HIGH?.put i v)) s0)

(* This one fails mysteriously,
   probably because some poor interaction of the well-formedness
   of the asserted formula itself and the tactic *)
[@expect_failure]
let test2_fails (i:nat) (v:mint) (s0:_) =
    assert (reify (let _ = HIGH?.put i v in
                   HIGH?.put i v) s0 ==
            bind_elab (reify (HIGH?.put i v))
                      (fun _ -> reify (HIGH?.put i v)) s0)
         by (tadmit())

//using an abbreviation for the asserted property works though
let test2 (i:nat) (v:mint) (s0:_) =
    assert (reify_bind_commutes (fun () -> HIGH?.put i v)
                                (fun () () -> HIGH?.put i v) s0)
        by (norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
            trefl())

let commutation_lemma
          (#a #b : _)
          (#wp1 : _) (c1:h_thunk a wp1)
          (#wp2 : _) (c2: (x:a -> h_thunk b (wp2 x))) (s0:_)
    : Lemma
         (requires (monotonic wp1 /\
                    (forall x. monotonic (wp2 x)) /\
                    HIGH?.bind_wp range0 _ _ wp1 wp2 s0 (fun _ -> True)))
         (ensures (reify_bind_commutes c1 c2 s0))
    = assert (reify_bind_commutes c1 c2 s0)
          by (dump "start";
              norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
              dump "after norm";
              trefl())
