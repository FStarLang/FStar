module Par_Triple

(*
  This module simplifies the Dijkstra Monads For All model in Par.fst.
  Instead of considering weakest preconditions, we here only consider
  Hoare triples.

    In short, we want parallel composition with the following (simplified) type

    val (<||>) (#a #b:Type)
               (#r0 #r1:resource)
               (#pre0:view r0 -> Type)
               (#pre1:view r1 -> Type)
               (#post0:a -> view r0 -> Type)
               (#post1:a -> view r1 -> Type)
               (c0:rst a r0 pre0 post0)
               (c1:rst b r1 pre1 post1)
             : RST (a & b) (r0 <*> r1) (pre0 /\ pre1) (post0 /\ post1)

*)

// The computational monad (free monad for the signature of { get , put , or }).
//
// This is a simple model of computation, supporting global state (2 locations
// storing natural numbers, locations modelled as booleans) and binary nondeterminism.
//
// Observe that parallel composition `||` is not part of the monad structure, because
// as is well known (cf the works of Plotkin et al), `||` is in fact a (binary) effect
// handler defined by recursion on the free monad structure (see below for details).


/// Proof sketch for soundness of locks
///
/// chi : Hoare triple interpretation of total correctness. Existing implementation, acquire/release encapsulated by get/put
///
/// step: state -> c:m a -> Terminates | Block
///
/// Total function, does not retry when blocking. If we try to acquire a blocked lock, we directly return blocking.
/// run_partial : state -> Terminates state | Blocking | Error =
///   step ...
///
/// Partial correctness proof
/// lemma_chi_characterization
///   (requires chi c /\ pre c)
///   (ensures Blocking? (run_partial c h) \/ Terminates? (run_partial /\ post run_partial))
///
/// Actual semantics, might not terminate. Blocks while waiting for to acquire locked resource
/// run: state -> Div (Terminates state | Error)
///   rec step ...
///
/// Final proof: Safety up to n steps of run w.r.t. chi.
/// This should be achieved using run_partial as an intermediate step
/// run_partial could be seen as run with "fuel 1", i.e. a non-recursive version





noeq
type m a =
  | Ret : a -> m a
  | Get : bool -> (nat -> m a) -> m a
  | Put : bool -> nat -> m a -> m a
  | MOr  : m a -> m a -> m a // MOr instead of Or to avoid name clashes with FStar.Reflection

// Functoriality of m
let rec map (#a:Type) (#b:Type) (f:a -> b) (c:m a) : Tot (m b) (decreases c) =
  match c with
  | Ret x -> Ret (f x)
  | Get b c -> Get b (fun n -> FStar.WellFounded.axiom1 c n; map f (c n))
  | Put b n c -> Put b n (map f c)
  | MOr c0 c1 -> MOr (map f c0) (map f c1)


// Below are two styles of defining the `||` operation. The first of these is more intuitive.

// Direct definition of parallel composition `||` as a combination of two mutually
// recursively defined left- and right-preferring parallel composition operators.
val l_par (#a:Type0) (#b:Type0) (c0:m a) (c1:m b) : Tot (m (a & b)) (decreases %[c0;c1])
val r_par (#a:Type0) (#b:Type0) (c0:m a) (c1:m b) : Tot (m (a & b)) (decreases %[c0;c1])

let pair_x (#a:Type) (x:a) = fun y -> (x, y)
let pair_y (#b:Type) (y:b) = fun x -> (x, y)

let rec l_get (#a:Type) (#b:Type) (c0':nat -> m a) (c1:m b) (n:nat) : Tot (m (a & b)) (decreases c0') =
  FStar.WellFounded.axiom1 c0' n;
  MOr (l_par (c0' n) c1) (r_par (c0' n) c1)

and l_par #a #b c0 c1 =
  match c0 with
  | Ret x -> map (pair_x x) c1
  | Get b c0' -> Get b (l_get c0' c1)
  | Put b n c0' -> Put b n (MOr (l_par c0' c1) (r_par c0' c1))
  | MOr c0' c0'' -> MOr (l_par c0' c1) (l_par c0'' c1)

and r_par #a #b c0 c1 =
  match c1 with
  | Ret y -> map (pair_y y) c0
  | Get b c1' -> Get b (fun n -> FStar.WellFounded.axiom1 c1' n; MOr (l_par c0 (c1' n)) (r_par c0 (c1' n)))
  | Put b n c1' -> Put b n (MOr (l_par c0 c1') (r_par c0 c1'))
  | MOr c1' c1'' -> MOr (r_par c0 c1') (r_par c0 c1'')

let m_par (#a #b:Type0) (c0:m a) (c1:m b) : m (a & b) =
  MOr (l_par c0 c1) (r_par c0 c1)

(*** Memory definitions ***)

/// For this example sketch, memory is simply a pair of booleans.
let mem = (f:(bool -> nat){FunctionalExtensionality.is_restricted bool f})

let upd (b:bool) (n:nat) (h:mem) : mem =
  FunctionalExtensionality.on_dom bool (fun b' -> if b = b' then n else h b')

let loc = option bool

let modifies (fp:loc) (h0 h1:mem) =
  match fp with
  | None -> True
  | Some b -> h0 (not b) == h1 (not b)

/// Separating conjunction of two resources.
let xor a b = (a || b) && ((not a) || (not b))

/// In the current model, two locations are disjoint if they are not the whole memory (None) and if they are actually disjoint (xor of two resources)
let disjoint (l1 l2:loc) = Some? l1 /\ Some? l2 /\ xor (Some?.v l1) (Some?.v l2)

/// l2 is included in l1
let includes (l1 l2:loc) =
  None? l1 \/ // l1 is the whole memory
  l1 == l2 // Or l1 is Some of something, and l2 needs to be the same

let loc_union (l1 l2:loc) : loc =
  match l1, l2 with
  | None, _ | _, None -> None
  | Some v1, Some v2 -> if v1 = v2 then Some v1 else None

/// We only consider predicates that are stable on the resource footprint: They depend only on the memory contents of the available resource
let is_stable_on (fp:loc) (pred:mem -> Type) =
  forall (h0 h1:mem) (l:loc). (pred h0 /\ modifies l h0 h1 /\ disjoint fp l) ==> pred h1

(*** Resource definitions ***)

/// Simple variant of our notion of resources.
let inv_reads_fp (fp:option bool) (inv:mem -> Type0) =
  forall h h' l. inv h /\ disjoint fp l /\ modifies l h h' ==> inv h'

noeq
type view_t a = {
  fp : option bool; (* none denotes owning both locations, TODO: account properly for owning neither location *)
  inv : mem -> Type0;
  sel : mem -> a
}

let view_t_refined a =
  view:view_t a{inv_reads_fp view.fp view.inv}

noeq
type resource = {
    t:Type0;
    view:view_t_refined t
  }

let (<*>) (r0 r1:resource) : resource =
  let t = r0.t & r1.t in
  let fp = None in
  let inv h = r0.view.inv h /\ r1.view.inv h /\
              Some? r0.view.fp /\ Some? r1.view.fp /\
              xor (Some?.v r0.view.fp) (Some?.v r1.view.fp)
  in
  let sel h = (r0.view.sel h,r1.view.sel h) in
  {
    t = t;
    view = {
      fp = fp;
      inv = inv;
      sel = sel
    }
  }

(*** Axiomatisation of the semantics, RST monad definition ***)

/// We assume here that the initial and final resources are the same
let rec chi #a (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (h_init h_current:mem) : Type =
  match c with
  | Ret x -> pre h_init ==> post h_current

  | Get b c ->
        includes r.view.fp (Some b) /\ // The accessed memory is inside the resource

        (FStar.WellFounded.axiom1 c (h_current b);
        chi (c (h_current b)) r pre post h_init h_current)

  | Put b n c ->
        includes r.view.fp (Some b) /\ // The updated memory is inside the resource
        // TODO: Equivalence is probably too strong. Should we rephrase chi to be {r.view.inv /\ pre}c{post /\ r.view.inv}
        // with resource invariants somehow outside of chi?
        (r.view.inv h_current <==> r.view.inv (upd b n h_current)) /\ // The resource invariant is preserved

        chi c r pre post h_init (upd b n h_current)

  | MOr c0 c1 -> chi c0 r pre post h_init h_current /\ chi c1 r pre post h_init h_current


let r_pred (pred:mem -> Type) (r:resource) = fun h -> pred h /\ r.view.inv h

/// The `is_stable_on predicate` is not yet provable in the current RST model:
/// pre/postconditions can currently refer to the whole memory, and not just the resource footprint
/// This will be resolved once selectors are implemented
let rst (a:Type) (r:resource) (pre post:mem -> Type) = c:m a{
  (forall h. chi c r (r_pred pre r) (r_pred post r) h h) /\
  is_stable_on r.view.fp pre /\ is_stable_on r.view.fp post}

(*** Denotational semantics ***)


/// Semantics of the monad
/// To resolve non-determinism for MOr, we might need a stream of booleans to pick the left or right branch at each or instruction
let rec run #a (c:m a) (h:mem) (pos:nat) (stream:nat -> bool) : a * mem =
  match c with
  | Ret x -> x, h
  | Get b c -> run (FStar.WellFounded.axiom1 c (h b); c (h b)) h pos stream
  | Put b n c -> run c (upd b n h) pos stream
  | MOr c0 c1 -> match stream pos with
                | false -> run c0 h (pos + 1) stream
                | true -> run c1 h (pos + 1) stream

/// The denotational semantics `run` and their axiomatisation `chi` should be coherent
/// More precisely, if we satisfy chi, then running the command `c` in a state satisfying the precondition
/// results in a state satisfying the postcondition, and only modifying the specified footprint
/// This would prove that Hoare triples accepted by chi always match the semantics
val lemma_chi_characterization (#a:Type) (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (h0:mem) (pos:nat) (stream:nat -> bool) : Lemma
  (requires pre h0 /\ chi c r pre post h0 h0)
  (ensures (
    let x, h1 = run c h0 pos stream in
    post h1 /\ modifies r.view.fp h0 h1)
  )

val lemma_chi_characterization_aux (#a:Type) (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (h0 h_current:mem) (pos:nat) (stream:nat -> bool) : Lemma
  (requires pre h0 /\ chi c r pre post h0 h_current)
  (ensures (
    let x, h1 = run c h_current pos stream in
    post h1 /\ modifies r.view.fp h_current h1)
  )


let rec lemma_chi_characterization_aux #a c r pre post h0 h_current pos stream =
  match c with
  | Ret x -> ()
  | Get b c -> FStar.WellFounded.axiom1 c (h_current b); lemma_chi_characterization_aux (c (h_current b)) r pre post h0 h_current pos stream
  | Put b n c -> lemma_chi_characterization_aux c r pre post h0 (upd b n h_current) pos stream
  | MOr c0 c1 -> match stream pos with
    | false -> lemma_chi_characterization_aux c0 r pre post h0 h_current (pos + 1) stream
    | true -> lemma_chi_characterization_aux c1 r pre post h0 h_current (pos + 1) stream

let lemma_chi_characterization #a c r pre post h0 pos stream = lemma_chi_characterization_aux #a c r pre post h0 h0 pos stream

(*** Lemmas about chi ***)

/// Map preserves chi
let rec map_chi (#a:Type) (#b:Type) (f:a -> b) (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (h_init h_current:mem) :
  Lemma
  (requires chi c r pre post h_init h_current)
  (ensures chi (map f c) r pre post h_init h_current)
  (decreases c) =
  match c with
  | Ret x -> ()
  | Get b c' ->
        FStar.WellFounded.axiom1 c' (h_current b); map_chi f (c' (h_current b)) r pre post h_init h_current
  | Put b n c -> map_chi f c r pre post h_init (upd b n h_current)
  | MOr c0 c1 -> map_chi f c0 r pre post h_init h_current; map_chi f c1 r pre post h_init h_current

/// We can derive a weaker precondition from a stronger one
let rec chi_weaken_post (#a:Type) (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (post_weak:mem -> Type) (h_init h_current:mem)
  : Lemma
  (requires chi c r pre post h_init h_current /\ (forall h. post h ==> post_weak h))
  (ensures chi c r pre post_weak h_init h_current)
  (decreases c) =
  match c with
  | Ret _ -> ()
  | Get b c' ->
    FStar.WellFounded.axiom1 c' (h_current b); chi_weaken_post (c' (h_current b)) r pre post post_weak h_init h_current
  | Put b n c -> chi_weaken_post c r pre post post_weak h_init (upd b n h_current)
  | MOr c0 c1 -> chi_weaken_post c0 r pre post post_weak h_init h_current; chi_weaken_post c1 r pre post post_weak h_init h_current

/// chi still holds if we strengthen the precondition
let rec chi_stronger_pre (#a:Type) (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (pre_strong:mem -> Type) (h_init h_current:mem)
  : Lemma
  (requires chi c r pre post h_init h_current /\ (forall h. pre_strong h ==> pre h))
  (ensures chi c r pre_strong post h_init h_current)
  (decreases c) =
  match c with
  | Ret _ -> ()
  | Get b c' ->
      FStar.WellFounded.axiom1 c' (h_current b); chi_stronger_pre (c' (h_current b)) r pre post pre_strong h_init h_current
  | Put b n c -> chi_stronger_pre c r pre post pre_strong h_init (upd b n h_current)
  | MOr c0 c1 -> chi_stronger_pre c0 r pre post pre_strong h_init h_current; chi_stronger_pre c1 r pre post pre_strong h_init h_current


/// If a subset of pre implies a new post for any memory, then chi still holds when the new post is added to the existing postcondition
let rec chi_pre_implies_post (#a:Type) (c:m a) (r:resource) (l:loc) (pre:mem -> Type) (pre_small:mem -> Type) (post:mem -> Type) (post_add:mem -> Type) (h_init h_current:mem)
  : Lemma
  (requires chi c r pre post h_init h_current /\
            (pre h_init ==> pre_small h_init) /\
            (pre_small h_init ==> post_add h_current) /\
            is_stable_on l pre_small /\
            is_stable_on l post_add /\
            disjoint l r.view.fp)
  (ensures chi c r pre (fun h -> post h /\ post_add h) h_init h_current)
  (decreases c) =
  match c with
  | Ret _ -> ()

  | Get b c' ->
    FStar.WellFounded.axiom1 c' (h_current b); chi_pre_implies_post (c' (h_current b)) r l pre pre_small post post_add h_init h_current

  | Put b n c ->
    assert (modifies r.view.fp h_current (upd b n h_current));
    chi_pre_implies_post c r l pre pre_small post post_add h_init (upd b n h_current)

  | MOr c0 c1 -> chi_pre_implies_post c0 r l pre pre_small post post_add h_init h_current; chi_pre_implies_post c1 r l pre pre_small post post_add h_init h_current


/// We can extend the resource in chi to a starred resource
let rec chi_bigger_resource (#a:Type) (c:m a) (r0 r1:resource) (pre:mem -> Type) (post:mem -> Type) (h_init h_current:mem)
  : Lemma
  (requires chi c r1 pre post h_init h_current /\ disjoint r0.view.fp r1.view.fp)
  (ensures chi c (r0 <*> r1) pre post h_init h_current /\ chi c (r1 <*> r0) pre post h_init h_current)
  (decreases c)
  =  match c with
  | Ret _ -> ()
  | Get b c' ->
      FStar.WellFounded.axiom1 c' (h_current b); chi_bigger_resource (c' (h_current b)) r0 r1 pre post h_init h_current
  | Put b n c ->
    let h' = upd b n h_current in
    assert (modifies (r1.view.fp) h_current h');
    assert (modifies r1.view.fp h' h_current);
    chi_bigger_resource c r0 r1 pre post h_init h'
  | MOr c0 c1 -> chi_bigger_resource c0 r0 r1 pre post h_init h_current; chi_bigger_resource c1 r0 r1 pre post h_init h_current

/// If c is valid and the current memory is modified in a disjoint location, then chi is still valid
let rec chi_modifies_disjoint (#a:Type) (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (h_init h_current:mem)  (b':bool) (n':nat)
  : Lemma
  (requires chi c r pre post h_init h_current /\
    disjoint r.view.fp (Some b') /\
    is_stable_on r.view.fp post)
  (ensures chi c r pre post h_init (upd b' n' h_current))
  (decreases c)
  =
  match c with

  | Ret _ -> assert (modifies (Some b') h_current (upd b' n' h_current))
  | Get b c' ->
      FStar.WellFounded.axiom1 c' (h_current b); chi_modifies_disjoint (c' (h_current b)) r pre post h_init h_current b' n'
  | Put b n c ->
    let h' = upd b n h_current in
    chi_modifies_disjoint c r pre post h_init h' b' n';

    FunctionalExtensionality.extensionality bool (fun _ -> nat)
      (upd b n (upd b' n' h_current)) (upd b' n' (upd b n h_current));
    let h_new = upd b' n' h_current in
    assert (modifies (Some b') h_new h_current);
    assert (modifies (Some b') h_current h_new);
    assert (modifies (Some b') (upd b n h_current) (upd b n h_new));
    assert (modifies (Some b') (upd b n h_new) (upd b n h_current))

  | MOr c0 c1 ->
        chi_modifies_disjoint c0 r pre post h_init h_current b' n';
        chi_modifies_disjoint c1 r pre post h_init h_current b' n'


let rec lemma_lpar (#a #b:Type)
    (r0:resource) (r1:resource{disjoint r0.view.fp r1.view.fp})
    (c0:m a) (c1:m b)
    (pre0 pre1 post0 post1:mem -> Type)
    (h_init h_current:mem) : Lemma
    (requires chi c0 r0 (r_pred pre0 r0) (r_pred post0 r0) h_init h_current /\ is_stable_on r0.view.fp pre0 /\ is_stable_on r0.view.fp post0 /\
      chi c1 r1 (r_pred pre1 r1) (r_pred post1 r1) h_init h_current /\ is_stable_on r1.view.fp pre1 /\ is_stable_on r1.view.fp post1)
    (ensures chi (l_par c0 c1) (r0 <*> r1) (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1)) (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1)) h_init h_current)
    (decreases %[c0; c1])
    = match c0 with
    | Ret x ->
      map_chi (pair_x x) c1 r1 (r_pred pre1 r1) (r_pred post1 r1) h_init h_current;
      chi_stronger_pre (l_par c0 c1) r1 (r_pred pre1 r1) (r_pred post1 r1) (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1)) h_init h_current;
      chi_pre_implies_post (l_par c0 c1) r1 r0.view.fp
        (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1))
        (r_pred pre0 r0)
        (r_pred post1 r1) (r_pred post0 r0)
        h_init h_current;
      chi_weaken_post (l_par c0 c1) r1 (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1))
        (fun h -> r_pred post1 r1 h /\ r_pred post0 r0 h) (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1))
        h_init h_current;
      chi_bigger_resource (l_par c0 c1) r0 r1 (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1)) (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1)) h_init h_current


    | Get b' c0' ->
      FStar.WellFounded.axiom1 c0' (h_current b');
      lemma_lpar r0 r1 (c0' (h_current b')) c1 pre0 pre1 post0 post1 h_init h_current;
      lemma_rpar r0 r1 (c0' (h_current b')) c1 pre0 pre1 post0 post1 h_init h_current

    | Put b' n c0' ->
      let r = r0 <*> r1 in

      chi_modifies_disjoint c1 r1 (r_pred pre1 r1) (r_pred post1 r1) h_init h_current b' n;
      lemma_lpar r0 r1 c0' c1 pre0 pre1 post0 post1 h_init (upd b' n h_current);
      lemma_rpar r0 r1 c0' c1 pre0 pre1 post0 post1 h_init (upd b' n h_current);

      assert (modifies r0.view.fp h_current (upd b' n h_current));
      assert (modifies r0.view.fp (upd b' n h_current) h_current)

    | MOr c0' c0'' -> lemma_lpar r0 r1 c0' c1 pre0 pre1 post0 post1 h_init h_current; lemma_lpar r0 r1 c0'' c1 pre0 pre1 post0 post1 h_init h_current

and lemma_rpar (#a #b:Type)
    (r0:resource) (r1:resource{disjoint r0.view.fp r1.view.fp})
    (c0:m a) (c1:m b)
    (pre0 pre1 post0 post1:mem -> Type)
    (h_init h_current:mem) : Lemma
    (requires chi c0 r0 (r_pred pre0 r0) (r_pred post0 r0) h_init h_current /\ is_stable_on r0.view.fp pre0 /\ is_stable_on r0.view.fp post0 /\
      chi c1 r1 (r_pred pre1 r1) (r_pred post1 r1) h_init h_current /\ is_stable_on r1.view.fp pre1 /\ is_stable_on r1.view.fp post1)
    (ensures chi (r_par c0 c1) (r0 <*> r1) (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1)) (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1)) h_init h_current)
    (decreases %[c0; c1])
    = match c1 with
    | Ret y ->
      map_chi (pair_y y) c0 r0 (r_pred pre0 r0) (r_pred post0 r0) h_init h_current;
      chi_stronger_pre (r_par c0 c1) r0 (r_pred pre0 r0) (r_pred post0 r0) (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1)) h_init h_current;
      chi_pre_implies_post (r_par c0 c1) r0 r1.view.fp
        (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1))
        (r_pred pre1 r1)
        (r_pred post0 r0) (r_pred post1 r1)
        h_init h_current;
      chi_weaken_post (r_par c0 c1) r0 (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1))
        (fun h -> r_pred post0 r0 h /\ r_pred post1 r1 h) (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1)) h_init h_current;
      chi_bigger_resource (r_par c0 c1) r1 r0 (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1)) (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1)) h_init h_current

    | Get b' c1' ->
        FStar.WellFounded.axiom1 c1' (h_current b');
        lemma_lpar r0 r1 c0 (c1' (h_current b')) pre0 pre1 post0 post1 h_init h_current;
        lemma_rpar r0 r1 c0 (c1' (h_current b')) pre0 pre1 post0 post1 h_init h_current

    | Put b' n c1' ->
      let r = r0 <*> r1 in

      chi_modifies_disjoint c0 r0 (r_pred pre0 r0) (r_pred post0 r0) h_init h_current b' n;

      lemma_lpar r0 r1 c0 c1' pre0 pre1 post0 post1 h_init (upd b' n h_current);
      lemma_rpar r0 r1 c0 c1' pre0 pre1 post0 post1 h_init (upd b' n h_current);

      assert (modifies r1.view.fp h_current (upd b' n h_current));
      assert (modifies r1.view.fp (upd b' n h_current) h_current)


    | MOr c1' c1'' ->
          lemma_rpar r0 r1 c0 c1' pre0 pre1 post0 post1 h_init h_current;
          lemma_rpar r0 r1 c0 c1'' pre0 pre1 post0 post1 h_init h_current

(*** Parallel composition ***)

/// This is where we enforce that we can only perform parallel composition of commands operating on resources with disjoint footprints
/// If memory footprints overlapped, we wouldn't be able to prove that assuming only both preconditions, we can prove both postconditions
/// through any interleaving (modeled by chi)
val par  (#a #b:Type0)
         (#r0:resource)
         (#r1:resource{disjoint r0.view.fp r1.view.fp})
         (#pre0 #pre1 #post0 #post1:mem -> Type)
         (c0:rst a r0 pre0 post0)
         (c1:rst b r1 pre1 post1)
       : rst (a & b) (r0 <*> r1) (fun h -> pre0 h /\ pre1 h) (fun h -> post0 h /\ post1 h)

let par #a #b #r0 #r1 #pre0 #pre1 #post0 #post1 c0 c1 =
  let c = m_par c0 c1 in
  let aux1 (h:mem) : Lemma
    (chi (l_par c0 c1) (r0 <*> r1)
      (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1))
      (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1))
      h h)
    = lemma_lpar r0 r1 c0 c1 pre0 pre1 post0 post1 h h in
  let aux2 (h:mem) : Lemma
    (chi (r_par c0 c1) (r0 <*> r1)
      (r_pred (fun h -> pre0 h /\ pre1 h) (r0 <*> r1))
      (r_pred (fun h -> post0 h /\ post1 h) (r0 <*> r1))
      h h)
    = lemma_rpar r0 r1 c0 c1 pre0 pre1 post0 post1 h h in
  Classical.forall_intro aux1;
  Classical.forall_intro aux2;
  c
