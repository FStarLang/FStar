module Par

(*

    A proof of concept implementation of concurrency (parallel composition `||`)
    based on the (unary) RST effect and resources, following the semantic 
    framework of Dijkstra Monads For All, i.e., deriving the Dijkstra monad 
    from an effect observation between a computational monad (the free monad 
    for the signature of {get,put,or}) and a specification monad (the weakest 
    precondition transformer monad for state and nondeterminism).

    In short, we want parallel composition with the following (simplified) type

    val (<||>) (#a #b:Type) 
               (#r0 #r1:resource) 
               (#wp0:rst_w a r0)
               (#wp1:rst_w b r1)
               (c0:rst a r0 wp0)
               (c1:rst b r1 wp1)
             : RST (a & b) (r0 <*> r1) (fun p h -> wp0 p h /\ wp1 p h)

    which we will in due course extend to the full RST indexed by two resources.

    For production code, we will likely just assume this operation, so as to 
    ensure compatibility and interoperability with current Low* heap and ST.

    But for showing that such axiomatic assumption is sound, we will develop
    in parallel a model of a fragment of Steel (Low* v3), in which such parallel 
    composition operation is definable within F*, a sketch of which is below.
    One can look this as doing a form of corresponding metatheory as a shallow 
    embedding within F* rather than on pen-and-paper (or as a deep embedding).

*)

// The computational monad (free monad for the signature of { get , put , or }).
//
// This is a simple model of computation, supporting global state (2 locations 
// storing natural numbers, locations modelled as booleans) and binary nondeterminism.
//
// Observe that parallel composition `||` is not part of the monad structure, because 
// as is well known (cf the works of Plotkin et al), `||` is in fact a (binary) effect 
// handler defined by recursion on the free monad structure (see below for details).
noeq 
type m a = 
  | Ret : a -> m a
  | Get : bool -> (nat -> m a) -> m a
  | Put : bool -> nat -> m a -> m a
  | Or  : m a -> m a -> m a

// Functoriality of m
let rec map (#a:Type) (#b:Type) (f:a -> b) (c:m a) : Tot (m b) (decreases c) =
  match c with
  | Ret x -> Ret (f x)
  | Get b c -> Get b (fun n -> FStar.WellFounded.axiom1 c n; map f (c n))
  | Put b n c -> Put b n (map f c)
  | Or c0 c1 -> Or (map f c0) (map f c1)


// Below are two styles of defining the `||` operation. The first of these is more intuitive.

// Direct definition of parallel composition `||` as a combination of two mutually
// recursively defined left- and right-preferring parallel composition operators.
val l_par (#a:Type0) (#b:Type0) (c0:m a) (c1:m b) : Tot (m (a & b)) (decreases %[c0;c1])
val r_par (#a:Type0) (#b:Type0) (c0:m a) (c1:m b) : Tot (m (a & b)) (decreases %[c0;c1])

let rec l_par #a #b c0 c1 = 
  match c0 with 
  | Ret x -> map (fun y -> (x,y)) c1
  | Get b c0' -> Get b (fun n -> FStar.WellFounded.axiom1 c0' n; Or (l_par (c0' n) c1) (r_par (c0' n) c1))
  | Put b n c0' -> Put b n (Or (l_par c0' c1) (r_par c0' c1))
  | Or c0' c0'' -> Or (l_par c0' c1) (l_par c0'' c1)
  
and r_par #a #b c0 c1 =
  match c1 with 
  | Ret y -> map (fun x -> (x,y)) c0
  | Get b c1' -> Get b (fun n -> FStar.WellFounded.axiom1 c1' n; Or (l_par c0 (c1' n)) (r_par c0 (c1' n)))
  | Put b n c1' -> Put b n (Or (l_par c0 c1') (r_par c0 c1'))
  | Or c1' c1'' -> Or (r_par c0 c1') (r_par c0 c1'')

let m_par (#a #b:Type0) (c0:m a) (c1:m b) = 
  Or (l_par c0 c1) (r_par c0 c1)

// A logically equivalent definition of parallel composition (at unit)
// in terms of two unary effect handlers, based on G. Plotkin's slides.
val r_par' (c0:m unit) (c1:m unit -> m unit) : m unit
let rec r_par' c0 c1 = 
  match c0 with
  | Ret x -> Ret x
  | Get b c0' -> Get b (fun n -> 
                          FStar.WellFounded.axiom1 c0' n;
                          Or (c1 (c0' n)) 
                             (r_par' (c0' n) c1))
  | Put b n c0' -> Put b n (Or (c1 c0') (r_par' c0' c1))
  | Or c0' c0'' -> Or (r_par' c0' c1) (r_par' c0'' c1)

val l_par' (c0:m unit) (c1:m unit) : m unit
let rec l_par' c0 c1 =
  match c0 with
  | Ret x -> Ret x
  | Get b c0' -> Get b (fun n -> 
                          FStar.WellFounded.axiom1 c0' n; 
                          Or (l_par' (c0' n) c1) 
                             (r_par' c1 (l_par' (c0' n))))
  | Put b n c0' -> Put b n (Or (l_par' c0' c1) (r_par' c1 (l_par' c0')))
  | Or c0' c0'' -> Or (l_par' c0' c1) (l_par' c0'' c1)

let m_par' c0 c1 : m unit = 
  Or (l_par' c0 c1) (r_par' c1 (l_par' c0))


// Now that we have the computational monad, we also need to define 
// a specification monad (i.e., monad of predicate transformers), 
// and then package them up as a Dijkstra monad RST using the Dijkstra 
// Monads For All framework developed in https://arxiv.org/abs/1903.01237.

// To this end, we proceed in two steps. We first define a predicate 
// transformer monad `w` and then an effect observation `theta : m -> w`.

// For this example sketch, memory is simply a pair of booleans.
let mem = bool -> nat

let upd (b:bool) (n:nat) (h:mem) : mem = 
  fun b' -> if b = b' then n else h b'

let modifies (fp:option bool) (h0 h1:mem) = 
  match fp with
  | None -> True
  | Some b -> h0 (not b) == h1 (not b)

// The specification monad `w` (omitting its return, bind, etc operations).
let w a = (a -> mem -> Type0) -> mem -> Type0

// The effect observation `theta` (mem-valued state with demonic nondeterminism).
let rec theta #a (c:m a) : w a = 
  match c with
  | Ret x -> 
      fun p h -> p x h
  | Get b c -> 
      fun p h -> 
        FStar.WellFounded.axiom1 c (h b);
        theta (c (h b)) p h
  | Put b n c -> 
      fun p h ->
        theta c p (upd b n h) //(fun b' -> if b = b' then n else h b')
  | Or c0 c1 -> 
      fun p h -> theta c0 p h /\ theta c1 p h                   // demonic nondeterminism

// The Dijkstra monad derived from `theta` following https://arxiv.org/abs/1903.01237.
//
// Below we define the (unary) RST effect as a layered effect on top of `d`.
let d (a:Type) (wp:w a) =
  c:m a{forall p h . wp p h ==> theta c p h}

// Simple variant of our notion of resources.
let inv_reads_fp (fp:option bool) (inv:mem -> Type0) =
  match fp with 
  | None -> True
  | Some b -> forall h h' . inv h /\ modifies (Some (not b)) h h' ==> inv h'

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

// Resource for a single location.
let loc_resource b = 
  let fp = Some b in
  let inv h = True in
  let sel h = h b in
  {
    t = nat;
    view = {
      fp = fp;
      inv = inv;
      sel = sel
    }
  }

// Separating conjunction of two resources.
let xor a b = (a || b) && ((not a) || (not b))

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

// The (unary) RST effect is defined on top of the Dijkstra monad derived above.
let imem (inv:mem -> Type0) = h:mem{inv h}

let rst_w (a:Type) (r:resource) = h:imem r.view.inv -> (a -> h':imem r.view.inv{modifies r.view.fp h h'} -> Type0) -> Type0


let rst (a:Type) (r:resource) (wp:rst_w a r) =
  d a (fun p h -> 
         r.view.inv h /\ 
         wp h (fun x h' -> r.view.inv h' /\ modifies r.view.fp h h' ==> p x h'))

// The RST effect comes with expected operations.
let return (#a:Type) (#r:resource) (x:a) : rst a r (fun h p -> p x h) =
  Ret x

let bind (#a:Type) (#b:Type) 
         (#r:resource) 
         (#wp0:rst_w a r) 
         (#wp1:a -> rst_w b r)
         (c0:rst a r wp0)
         (c1:(x:a -> rst b r (wp1 x)))
       : rst b r (fun h p -> wp0 h (fun x h' -> wp1 x h' p)) = 
  admit ()     // TODO: implement bind, likely need to restrict `rst_w` to monotonic predicate transformers

let get b : rst nat (loc_resource b) (fun h p -> p (h b) h) =
  Get b (fun n -> Ret n)

let put b n : rst unit (loc_resource b) (fun h p -> p () (upd b n h)) =
  Put b n (Ret ())


// Some lemmas about the expected behaviour of framing resource invariants across modifies.
// Not being able to prove these results before lead to the non-verification of the spec of `||` .

let lemma_modifies_star_left (r0 r1:resource) (h h':mem)
  : Lemma (requires ((r0 <*> r1).view.inv h /\ modifies r0.view.fp h h' /\ r0.view.inv h'))
          (ensures  ((r0 <*> r1).view.inv h')) = 
  ()

let lemma_modifies_star_right (r0 r1:resource) (h h':mem)
  : Lemma (requires ((r0 <*> r1).view.inv h /\ modifies r1.view.fp h h' /\ r1.view.inv h'))
          (ensures  ((r0 <*> r1).view.inv h')) = 
  ()

// Parallel composition that splits the given resource up between the two threads.
val par (#a:Type0) (#b:Type0) 
        (#r0 #r1:resource) 
        (#wp0:rst_w a r0)
        (#wp1:rst_w b r1)
        (c0:rst a r0 wp0)
        (c1:rst b r1 wp1)
      : rst (a & b) (r0 <*> r1) (fun h p -> 
                                  wp0 h (fun x h' -> wp1 h' (fun y h'' -> p (x,y) h'')) /\ 
                                  wp1 h (fun y h' -> wp0 h' (fun x h'' -> p (x,y) h''))) 

// Having earlier found a bug in the definition of `<*>` above, 
// this definition of parallel composition currently fails.  
//
// My guess is that we need some additional lemmas about the  
// interaction of theta, and `l_par`, `r_par`, and `m_par` (or 
// define `l_par`, `r_par`, and `m_par` here directly with suitable 
// RST effect types). To this end, we might also need to refine the
// definition of `rst_w` to only contain WPs that are commutative   
// when their resources are disjoint (such as separated by `<*>`).
[@expect_failure]
let par #a #b #r0 #r1 #wp0 #wp1 c0 c1 =
  m_par #a #b c0 c1
