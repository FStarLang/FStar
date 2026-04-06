module TestST

let state_t = int

let post a = a -> state_t -> Type0
let pre = state_t -> Type0

(* The spec monad *)
let spec (a:Type) = post a -> pre

unfold
let return_spec (a:Type) (x:a) : spec a = fun p s -> p x s

unfold
let bind_spec (a b:Type) (w0:spec a) (w1:(a -> spec b)) : spec b =
  fun post -> w0 (fun x -> w1 x post)

(* Subsumption on specs *)
let stronger (#a:Type) (w1 w2 : spec a) = forall s0 p. w1 s0 p ==> w2 s0 p

(* The computation monad, indexed by spec *)
let st (a:Type) (w:spec a) = p:post a -> s0:state_t{ w p s0 } -> x:(a & state_t) { p (fst x) (snd x) }

(* Proving that spec and computation are related: This is what I mean by proving combinators sound *)
let return (a:Type) (x:a) : st a (return_spec a x) = fun _ s -> x, s

let bind (a b:Type) (w0: spec a) (w1:a -> spec b) 
         (f:st a w0) (g:(x:a -> st b (w1 x)))
: st b (bind_spec a b w0 w1)
= fun post s0 ->
    let x, s1 = f (fun x -> w1 x post) s0 in
    g x post s1

(* Subsumption as a combinator of the computation monad *)
let subcomp
  (a:Type)
  (wpf wpg : spec a)
  (f : st a wpf)
  : Pure (st a wpg)
         (requires (stronger wpg wpf))
         (ensures (fun _ -> True))
  = f

let sub #a (#w0 #w1:spec a) ($f: st a w0) (#_:squash (stronger w1 w0))
: st a w1
= subcomp _ _ _ f


(* Now, you can package all this up with F*'s analog of do-noation (let! etc.
   similar to what OCaml provides) *)
let (let!) (#a #b:Type) (#w0: spec a) (#w1:a -> spec b) 
           (f:st a w0) (g:(x:a -> st b (w1 x)))
: st b (bind_spec a b w0 w1)
= bind a b w0 w1 f g

let ret #a (x:a) : st a (return_spec a x) = return a x

(* An also define some actions *)
unfold
let get_spec : spec state_t = fun post s0 -> post s0 s0
let get : st state_t get_spec = fun post s0 -> s0, s0

unfold
let put_spec (x:state_t) : spec unit = fun post s0 -> post () x
let put (s:state_t) : st unit (put_spec s) = fun post s0 -> (), s


(* And now we can write some programs, infer their VCs etc.
   all fully verified, just using F*'s type inference for pure
   terms: Nothing special here *)
let test : st unit (bind_spec _ _ get_spec put_spec) =
  let! s0 = get in
  put s0

(* st terms are just monadic terms that reduce as normal.
   So you can just compute with them as well *)
let run #a (#w:spec a) (s:st a w) (s0:_{ w (fun _ _ -> True) s0}) : a & state_t = 
  s (fun _ _ -> True) s0

let test_alt_assert () = 
  assert_norm (run test 17 == ((), 17))

(* But, this is a bit tedious to use. E.g., you have to apply subsumption manually *)
let id_spec : spec unit = fun post s0 -> post () s0
let test_alt : st unit id_spec =
  sub (
    let! s0 = get in
    put (s0 + 1) ;!
    put s0
  )

(* So, what F* also lets you do is to package these definitions into an effect,
  and then some built-in compiler machinery kicks in and will infer VCs using
  the combinators provided, apply subsumption when needed, return pure values
  into ST etc. *)

total (* ST computation are proven terminating *)
reifiable (* You can access their monadic representation *)
reflectable (* You can lift monadic code to the effect *)
effect {
  ST (a:Type) (w:spec a)
  with {repr=st; return; bind; subcomp}
}

open FStar.Monotonic.Pure
unfold
let lift_wp (#a:Type u#a) (w:pure_wp a) : spec a =
  fun p s0 -> w (fun x -> p x s0)

let lift_pure_st (a:Type u#a) wp (f : unit -> PURE a wp)
  : st a (lift_wp wp)
  = elim_pure_wp_monotonicity_forall u#a ();
    fun p s0 -> (f (), s0)

(* This bit tells F* to return pure computations into ST automatically *)
sub_effect PURE ~> ST = lift_pure_st

(* You can use monadic reflection to lift the actions into ST *)
let get_st () : ST state_t get_spec = ST?.reflect get
let put_st (x:state_t) : ST unit (put_spec x) = ST?.reflect (put x)

(* And now write programs in ML-style CBV notation with VCs inferred *)
let test_st () : ST unit id_spec =
  let s0 = get_st () in
  put_st (s0 + 1);
  put_st s0