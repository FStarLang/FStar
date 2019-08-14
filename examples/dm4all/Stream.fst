module Stream

(**********************************************************************************)
(* Before defining streams, a bit of boilerplate to define the greatest fixpoint  *)
(* (nu f) of a monotonic function f on predicates                                 *)
(**********************************************************************************)

let nu (#a:Type) (f : ((a -> prop) -> a -> prop)) (x:a) : prop =
  exists (p : a -> prop). (forall x'. p x' ==> f p x') /\ p x

let monotonic (#a:Type) (f : ((a -> prop) -> a -> prop)) : prop =
  forall (p1 p2: (a -> prop)). (forall x. p1 x ==> p2 x) ==> (forall x. f p1 x ==> f p2 x)

let nu1 (#a:Type) (f : ((a -> prop) -> a -> prop)) (x:a) : prop =
  exists (p : a -> prop). (forall x'. p x' ==> f p x') /\ f p x

let nu_nu1 (#a:Type) (f : ((a -> prop) -> a -> prop))
: Lemma (forall x. nu f x ==> nu1 f x) = ()

let mon_sup (#a #b:Type) (f : ((a -> prop) -> a -> prop)) (p : b -> a -> prop)
  : Lemma (requires monotonic f) (ensures (forall y. (exists x. f (p x) y) ==> f (fun y -> exists x. p x y) y)) = ()

let mon_sup' (#a #b:Type) (f : ((a -> prop) -> a -> prop)) (q: b -> prop) (p : b -> a -> prop)
 : Lemma (requires monotonic f) (ensures (forall y. (exists x. q x /\ f (p x) y) ==> f (fun y -> exists x. q x /\ p x y) y)) = ()

let nu_fixpoint0 (#a:Type) (f : ((a -> prop) -> a -> prop))
  : Lemma (requires (monotonic f)) (ensures (forall x. nu f x ==> f (nu f) x)) =
  nu_nu1 f ; mon_sup' f (fun p -> forall x'. p x' ==> f p x') (fun p x -> p x)

let nu_fixpoint1 (#a:Type) (f : ((a -> prop) -> a -> prop))
  : Lemma (requires (monotonic f)) (ensures (forall x. f (nu f) x ==> nu f x)) =
  nu_fixpoint0 f

let nu_fixpoint (#a:Type) (f : ((a -> prop) -> a -> prop))
  : Lemma (requires (monotonic f)) (ensures (forall x. f (nu f) x <==> nu f x)) =
  nu_fixpoint0 f ; nu_fixpoint1 f

open FStar.Classical

let nu_greatest (#a:Type) (f : ((a -> prop) -> a -> prop)) (p : (a -> prop)) (hp : (x:a) -> Lemma (requires p x) (ensures f p x)) (x:a)
  : Lemma (requires p x) (ensures nu f x) =
  let hp' x : Lemma (p x ==> f p x) = move_requires hp x in
  forall_intro hp'





(**********************************************************************************)
(* This module define a type of stream (infinite lists) parametrized by their content *)
(**********************************************************************************)

assume val stream : Type -> Type

(* A stream can be observed with 2 operations
   - head returns the first element of the stream
   - tail returns all but the first element *)
assume val head : (#a:Type) -> stream a -> a
assume val tail : (#a:Type) -> stream a -> stream a


(* We can build a stream starting from a seed of some type s such that any
element of s can be projected to an element of the contained type and any
element can be "updated" *)
assume val build_stream : (#a:Type) -> (#s:Type) -> (s -> a) -> (s -> s) -> s -> stream a

(* We define the behaviour of this stream by its observations *)
assume HeadBuildStream : forall a s hd tl seed. head (build_stream #a #s hd tl seed) == hd seed
assume HeadBuildTail : forall a s hd tl seed. tail (build_stream #a #s hd tl seed) == build_stream #a #s hd tl (tl seed)

(* Finally we set the equality on streams to be bisimilarity,
   that is the biggest relation bisim such that related elements
   have the same head and related tails *)
let bisim0 (#a:Type) (bisim : stream a * stream a -> prop) ((s1,s2) : stream a * stream a) : prop =
  head s1 == head s2 /\ bisim (tail s1, tail s2)
let bisim = nu bisim0
assume StreamEqualityIsBisimulation : forall a (s1 s2 : stream a). s1 == s2 <==> bisim (s1,s2)

(* Do NOT put the following kind of axiom !!! *)
(* assume TailDecreases : forall a (s:stream a). tail s << s *)
(* let rec stupid (s:stream nat) : False = stupid (tail s) *)


(**********************************************************************************)
(* Functions on streams and their properties                                      *)
(**********************************************************************************)

(* Appending an element at the beginning of a stream *)
let comatch_stream0 (#a:Type) (x0:a) (s:stream a) (init : option (stream a)): stream a =
  build_stream #a #(option (stream a))
               (fun x -> match x with | None -> x0 | Some s -> head s)
               (fun x -> match x with | None -> Some s | Some s -> Some (tail s))
               init

let comatch_stream (#a:Type) (x0:a) (s:stream a) : stream a = comatch_stream0 x0 s None

let r (#a:Type) (x0:a) (s0:stream a) ((s1,s2):stream a * stream a) : prop = s2 == comatch_stream0 x0 s0 (Some s1)
let r_bisim0 (#a:Type) (x0:a) (s0:stream a) (s12:stream a * stream a) : Lemma (requires r x0 s0 s12) (ensures bisim0 (r x0 s0) s12) = ()

let comatch_stream0_some_lemma (#a:Type) (x0:a) (s0 s:stream a) : Lemma (s == comatch_stream0 x0 s0 (Some s)) =
  nu_greatest bisim0 (r x0 s0) (r_bisim0 x0 s0) (s, comatch_stream0 x0 s0 (Some s))

let tail_comatch_stream (#a:Type) (x0:a) (s0:stream a) : Lemma (tail (comatch_stream x0 s0) == s0) =
  comatch_stream0_some_lemma x0 s0 s0

(* Simple eta law for streams *)
let p (#a:Type) ((s1,s2):stream a * stream a) : prop =
  (head s2 == head s1 /\ tail s2 == tail s1) \/ s1 == s2

let p_bisim0 (#a:Type) (s12:stream a * stream a) : Lemma (requires p s12) (ensures bisim0 p s12) =
  ()

let stream_eta (#a:Type) (s:stream a) : Lemma (s == comatch_stream (head s) (tail s)) =
  let s' = comatch_stream (head s) (tail s) in
  assert (head s == head s') ;
  tail_comatch_stream (head s) (tail s) ;
  assert (tail s == tail s') ;
  assert (p (s, comatch_stream (head s) (tail s))) ;
  nu_greatest bisim0 p p_bisim0 (s, comatch_stream (head s) (tail s))

(* n-iterated tail of a stream *)
let rec ntail (n:nat) (#a:Type) (s:stream a) : stream a =
  if n = 0 then s else ntail (n-1) (tail s)

let rec ntail_tail (#a:Type) (s: stream a) (n:nat) : Lemma (requires True) (ensures (tail (ntail n s) == ntail (n+1) s)) (decreases n) =
  if n = 0 then () else ntail_tail (tail s) (n-1)

let ntail_lemma (#a:Type) (s s1 : stream a) : Lemma (requires (exists n. s1 == ntail n s)) (ensures (exists n. tail s1 == ntail n s)) =
  forall_intro (ntail_tail s)

let tails_of_s (#a:Type) (s0 s:stream a)  : prop = exists n. s == ntail n s0



(**********************************************************************************)
(* Examples of streams                                                            *)
(**********************************************************************************)

let build_nat_from (n0:nat) : stream nat = build_stream #nat #nat (fun n -> n) (fun n -> n+1) n0

let all_nats = build_nat_from 0

let _ = assert (head all_nats == 0)
let _ = assert (head (tail all_nats) == 1)
let _ = assert (head (tail (tail all_nats)) == 2)
let _ = assert (head (tail (tail (tail all_nats))) == 3)


let increasing0 (increasing : stream nat -> prop) (s:stream nat) : prop = head s < head (tail s) /\ increasing (tail s)
let increasing = nu increasing0

let p_all_nats_incr (s:stream nat) : prop = exists n. s == build_nat_from n
let p_all_nats_incr_lemma (s:stream nat) : Lemma (requires (p_all_nats_incr s)) (ensures increasing0 p_all_nats_incr s) = ()

let all_nats_incr () : Lemma (increasing all_nats) = nu_greatest increasing0 p_all_nats_incr p_all_nats_incr_lemma all_nats






// let _ = assert False


