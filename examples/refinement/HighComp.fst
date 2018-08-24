module HighComp

open FStar.Classical
open FStar.Tactics
open FStar.Reflection

module U32 = FStar.UInt32


type mint = U32.t
type state = mint * mint

// High-level specs live in [comp]
let comp a = state -> M (a * state)

// DSL combinators without WP indexing

let hreturn (a:Type) (x : a) : comp a = fun s -> (x, s)

let hbind (a:Type) (b:Type) (m : comp a) (f : a -> comp b) : comp b =
    fun s -> let (x, s1) = m s in f x s1

let hread (i:int) : comp mint =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)

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

type hwp a = HIGH?.wp a

let monotonic #a (wp:hwp a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2}
    (forall x.{:pattern (p1 x) \/ (p2 x)} p1 x ==> p2 x) ==>
    wp s p1 ==>
    wp s p2

type hwp_mon 'a = (wp:hwp 'a{monotonic wp})

// [comp] type with wp
type comp_wp 'a (wp : hwp_mon 'a) = s0:state -> PURE ('a * state) (wp s0)

unfold
let return_wp (#a:Type) (x : a) : hwp_mon a = HIGH?.return_wp a x

assume val range0: range

unfold
let bind_wp #a #b (wp1:hwp_mon a) (fwp2 : (a -> hwp_mon b)) : (wp:hwp_mon b) =
  HIGH?.bind_wp range0 a b wp1 fwp2

unfold
let read_wp (i:nat) : hwp_mon mint =
  fun s0 post -> post (hread i s0)

unfold
let write_wp (i:nat) (v:mint) : hwp_mon unit =
  fun s0 post -> post (hwrite i v s0)

unfold
let ite_wp #a (b : bool) (wp1 : hwp_mon a) (wp2 : hwp_mon a) : hwp_mon a =
  HIGH?.wp_if_then_else a b wp1 wp2

val for_wp : (int -> hwp_mon unit) -> (lo : int) -> (hi : int{hi >= lo}) -> Tot (hwp_mon unit) (decreases (hi - lo))
let rec for_wp (wp:int -> hwp_mon unit) (lo : int) (hi : int{hi >= lo}) : Tot (hwp_mon unit) (decreases (hi - lo)) = 
  if lo = hi then (return_wp ())
  else (bind_wp (wp lo) (fun (_:unit) -> for_wp wp (lo + 1) hi))
  

let for_wp_unfold (wp:int -> hwp_mon unit) (lo : int) (hi : int{hi >= lo}) : 
    Lemma (requires (lo < hi))
          (ensures (for_wp wp lo hi == bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi))) =
  assert (~ (lo = hi)); 
  assert ((if lo = hi then (return_wp ())
           else (bind_wp (wp lo) (fun (_:unit) -> for_wp wp (lo + 1) hi))) == 
           bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi)); 
           assert_norm (for_wp wp lo hi == 
                        (if lo = hi then (return_wp ())
                         else (bind_wp (wp lo) (fun (_:unit) -> for_wp wp (lo + 1) hi))))


// for combinator
let rec for (#wp : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> HIGH unit (wp i)) :
    HIGH unit (for_wp wp lo hi) (decreases (hi - lo)) =
  if lo = hi then ()
  else 
  (f lo; for #wp (lo + 1) hi f)


// High-level DSL with WP indexing

let return_elab (#a:Type) (x : a) : comp_wp a (return_wp x) =
  HIGH?.return_elab a x

let bind_elab #a #b #f_w ($f:comp_wp a f_w) #g_w ($g:(x:a) -> comp_wp b (g_w x)) : 
    Tot (comp_wp b (bind_wp f_w g_w)) = HIGH?.bind_elab a b f_w f g_w g



let rec for_elab (#wp : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> comp_wp unit (wp i)) : 
    Tot (comp_wp unit (for_wp wp lo hi)) (decreases (hi - lo)) =
  if lo = hi then (return_elab ())
  else (let (m : comp_wp unit (wp lo)) = f lo in 
        let f (u:unit) : comp_wp (unit) (for_wp wp (lo+1) hi) = for_elab #wp (lo + 1) hi f in
        let p = for_wp_unfold wp lo hi in 
        assert (for_wp wp lo hi == bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi));
        let b = bind_elab m f in b)


let rec for_elab_unfold (#wp : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> comp_wp unit (wp i)) : 
    Lemma (requires (lo < hi))
          (ensures (for_elab #wp lo hi f == 
                    (let (m : comp_wp unit (wp lo)) = f lo in 
                     let cf (u:unit) : comp_wp (unit) (for_wp wp (lo+1) hi) = for_elab #wp (lo + 1) hi f in
                     let p = for_wp_unfold wp lo hi in                    
                     bind_elab m cf))) =
  assert_norm (for_elab #wp lo hi f ==
               (if lo = hi then (return_elab ())
                else (let (m : comp_wp unit (wp lo)) = f lo in 
                      let f (u:unit) : comp_wp (unit) (for_wp wp (lo+1) hi) = for_elab #wp (lo + 1) hi f in
                      let p = for_wp_unfold wp lo hi in 
                      assert (for_wp wp lo hi == bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi));
                      bind_elab #unit #unit #(wp lo) m f)));
               ()
          

let hread' (i:nat) : comp_wp mint (read_wp i) =
  (fun s -> if i = 0 then (fst s, s) else (snd s, s))

let hwrite' (i:nat) (v:mint) : comp_wp unit (write_wp i v) =
  fun s -> if i = 0 then ((), (v, snd s))
        else ((), (fst s, v))

let put_action = HIGH?.put
let get_action = HIGH?.get

// Commutation
let h_eq (#a:Type) (wp1:hwp_mon a) (wp2:hwp_mon a) (c1:comp_wp a wp1) (c2:comp_wp a wp2) =
    (forall s0. wp1 s0 (fun _ -> True) <==> wp2 s0 (fun _ -> True)) /\
    (forall s0. wp1 s0 (fun _ -> True) ==> c1 s0 == c2 s0)

// Equivalence with reified computations

let hwrite_eq (#a:Type) (i:nat) (v:mint) :
   Lemma (h_eq (write_wp i v) (write_wp i v) (hwrite' i v) (reify (HIGH?.put i v))) = ()

let hread_eq (#a:Type) (i:nat) :
   Lemma (h_eq (read_wp i) (read_wp i) (hread' i) (reify (HIGH?.get i))) = ()


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

let test (i:nat) (v:mint) (s0:_) =
    assert (reify (let _ = HIGH?.put i v in
                   HIGH?.put i v) s0 ==
            bind_elab (reify (HIGH?.put i v))
                      (fun _ -> reify (HIGH?.put i v)) s0)

let test2_tac (i:nat) (v:mint) (s0:_) =
    assert (reify (let _ = HIGH?.put i v in
                   HIGH?.put i v) s0 ==
            bind_elab (reify (HIGH?.put i v))
                      (fun _ -> reify (HIGH?.put i v)) s0)
         by (norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
             trefl())

let test2_tac_again (i:nat) (v:mint) (s0:_) =
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

let ite_commutes_lemma (#a : Type) (b : bool)
      (#wp1 : hwp_mon a) ($c1:h_thunk a wp1)
      (#wp2 : hwp_mon a) ($c2:h_thunk a wp2) (s0:state) :
      Lemma (requires (ite_wp b wp1 wp2 s0 (fun _ -> True)))
            (ensures (reify_ite_commutes b c1 c2 s0)) = ()
