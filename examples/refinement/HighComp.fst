module HighComp

open FStar.Classical
open FStar.Tactics
open FStar.Reflection

module U32 = FStar.UInt32


type mint = U32.t
type state = mint * mint

// High-level specs live in [comp]
let comp a = state -> M (a * state)

type hwp 'a = state -> ('a * state -> Type) -> Type  // x:hwp a { monotonic x }

let monotonic #a (wp:hwp a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2} (forall x. p1 x ==> p2 x) ==> wp s p1 ==> wp s p2

type hwp_mon 'a = (wp:hwp 'a{monotonic wp}) 
  
// [comp] type with wp
type comp_wp 'a (wp : hwp_mon 'a) = s0:state -> PURE ('a * state) (wp s0)
type comp_wp' 'a (wp : hwp_mon 'a) = s0:state -> PURE ('a * state) (wp s0)

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


// WPs -- monotonic by construction 

unfold
let return_wp (#a:Type) (x : a) : wp:hwp a{monotonic wp} = 
  let wpr = fun s0 post -> post (x, s0) in
  let p : squash (monotonic wpr) = 
      let p (p1 : a * state -> Type) (p2 : a * state -> Type) (s : state) 
            (h: squash (forall y. p1 y ==> p2 y)) : GTot (squash (wpr s p1 ==> wpr s p2)) = 
          ()
      in
      let p' p1 p2 s : Lemma ((forall y. p1 y ==> p2 y) ==> (wpr s p1 ==> wpr s p2)) = 
      arrow_to_impl (p p1 p2 s)
      in
      forall_intro_3 p'
  in 
  assert (monotonic wpr);
  wpr

assume val range0: range

let bind_wp #a #b (wp1:hwp a{monotonic wp1}) (fwp2 : (a -> wp2:hwp b{monotonic wp2})) : (wp:hwp b{monotonic wp}) = 
  HIGH?.bind_wp range0 a b wp1 fwp2

let read_wp (i:nat) : wp:hwp mint{monotonic wp} = 
  fun s0 post -> post (hread i s0)

let write_wp (i:nat) (v:mint) : wp:hwp unit{monotonic wp} = 
  fun s0 post -> post (hwrite i v s0)

let ite_wp #a (b : bool) (wp1 : hwp a{monotonic wp1}) 
  (wp2 : hwp a{monotonic wp2}) : wp:hwp a{monotonic wp} = 
  HIGH?.wp_if_then_else a b wp1 wp2  

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

let return_elab (#a:Type) (x : a) : comp_wp a (return_wp x) = 
  HIGH?.return_elab a x

let bind_elab #a #b #f_w ($f:_) #g_w ($g:_) : comp_wp b (bind_wp f_w g_w) = HIGH?.bind_elab a b f_w f g_w g

val hread' : i:nat -> comp_wp mint (read_wp i)
let hread' (i:nat) : comp_wp mint (read_wp i) =
  (fun s -> if i = 0 then (fst s, s) else (snd s, s))

val hwrite' : i:nat -> v:mint -> comp_wp unit (write_wp i v)
let hwrite' (i:nat) (v:mint) : comp_wp unit (write_wp i v) =
  fun s -> if i = 0 then ((), (v, snd s))
        else ((), (fst s, v))

// Commutation
val h_eq : (#a:Type) -> (wp1:hwp a{monotonic wp1}) -> (wp2:hwp a{monotonic wp2}) -> (comp_wp a wp1) -> (comp_wp a wp2) -> GTot Type0
let h_eq #a wp1 wp2 c1 c2 =
    (forall s0. wp1 s0 (fun _ -> True) <==> wp2 s0 (fun _ -> True)) /\
    (forall s0. wp1 s0 (fun _ -> True) ==> wp2 s0 (fun _ -> True) /\ c1 s0 == c2 s0)

// Equivalence with reified computations

let hwrite_eq (#a:Type) (i:nat) (v:mint) :
   Lemma (h_eq (write_wp i v) (write_wp i v) (hwrite' i v) (reify (HIGH?.put i v))) = ()

let hread_eq (#a:Type) (i:nat) :
   Lemma (h_eq (read_wp i) (read_wp i) (hread' i) (reify (HIGH?.get i))) = ()


open FStar.Tactics

let h_thunk a (wp:hwp_mon a) = unit -> HIGH a wp

let reif (#a:Type) wp (c : h_thunk a wp) :
  comp_wp a wp = reify (c ())

let reify_bind_commutes
          (#a #b : _)
          (#wp1 : _) ($c1:h_thunk a wp1)
          (#wp2 : _) ($c2: (x:a -> h_thunk b (wp2 x)))
          (s0:_{bind_wp wp1 wp2 s0 (fun _ -> True)})
     = reify (let x = c1 () in c2 x ()) s0 ==
       bind_elab (reify (c1 ()))
                 (fun x -> reify (c2 x ())) s0


let ite_elab (#a:Type) (b : bool) (#wp1 : hwp_mon a) (c1:comp_wp a wp1) 
  (#wp2 : hwp_mon a) (c2:comp_wp a wp2) : comp_wp a (ite_wp b wp1 wp2) =
  (fun s0 -> if b then c1 s0 else c2 s0)

let ite_reif (#a:Type) (b : bool) (#wp1 : hwp_mon a) ($c1:h_thunk a wp1) 
  (#wp2 : hwp_mon a) ($c2:h_thunk a wp2) : comp_wp a (ite_wp b wp1 wp2) = 
  reify (if b then c1 () else c2 ())


let reify_ite_commutes (#a:Type) (b : bool) (#wp1 : hwp_mon a) ($c1:h_thunk a wp1) 
  (#wp2 : hwp_mon a) ($c2:h_thunk a wp2) (s0:_{ite_wp b wp1 wp2 s0 (fun _ -> True)}) =
  ite_reif b c1 c2 s0 == ite_elab b (reif wp1 c1) (reif wp2 c2) s0

[@expect_failure]
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
[@expect_failure]
let test2 (i:nat) (v:mint) (s0:_) =
    assert (reify_bind_commutes (fun () -> HIGH?.put i v)
                                (fun () () -> HIGH?.put i v) s0)
        by (norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
            trefl())

let bind_commutes_lemma
          (#a #b : _)
          (#wp1 : _) (c1:h_thunk a wp1)
          (#wp2 : _) (c2: (x:a -> h_thunk b (wp2 x))) (s0:_)
    : Lemma
         (requires (HIGH?.bind_wp range0 _ _ wp1 wp2 s0 (fun _ -> True)))
         (ensures (reify_bind_commutes c1 c2 s0))
    = assert (reify_bind_commutes c1 c2 s0)
          by (dump "start";
              norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
              dump "after norm";
              trefl())

let ite_commutes_lemma (#a #b : Type) (b : bool)
      (#wp1 : hwp_mon a) ($c1:h_thunk a wp1) 
      (#wp2 : hwp_mon a) ($c2:h_thunk a wp2) (s0:state) : 
      Lemma (requires (ite_wp b wp1 wp2 s0 (fun _ -> True)))
            (ensures (reify_ite_commutes b c1 c2 s0)) = ()
            
