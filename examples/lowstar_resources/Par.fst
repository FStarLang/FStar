module Par

(*

    A proof of concept implementation of concurrency (parallel composition)
    based on the (unary) RST effect and resources, following the semantic 
    framework of Dijkstra Monads For All, i.e., deriving the Dijkstra monad 
    from an effect observation between a computational monad (the free monad 
    for the signature of {get,put,or}) and a specification monad (the weakest 
    precondition transformer monad for state and nondeterminism).

    By the end, we will have parallel composition operator for (unary) RST:

    val (<||>) (#a #b:Type) 
               (#r0 #r1:resource) 
               (#wp0:rst_w a r0)
               (#wp1:rst_w b r1)
               (c0:rst a r0 wp0)
               (c1:rst b r1 wp1)
             : RST (a & b) (r0 <*> r1) (fun p h -> wp0 p h /\ wp1 p h)

*)

// The computational monad (free monad for the signature of { get , put , or }).
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

// Direct definition of parallel composition as a combination of two mutually
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

let m_par (#a #b:Type) (c0:m a) (c1:m b) = 
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

// Memory is simply a pair of booleans.
let mem = bool -> nat

// The specification monad.
let w a = (a -> mem -> prop) -> mem -> prop

// The effect observation (mem-valued state with demonic nondeterminism).
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
        theta c p (fun b' -> if b = b' then n else h b')
  | Or c0 c1 -> 
      fun p h -> theta c0 p h /\ theta c1 p h                   // demonic nondeterminism

// The Dijkstra monad derived from the effect observation above.
let d (a:Type) (wp:w a) =
  c:m a{forall p h . wp p h ==> theta c p h}

// Simple notion of resources (TODO: resource fp need to be extended to properly capture empty_resource).
noeq
type view_t a = {
  fp : option bool;
  inv : mem -> Type0;
  sel : mem -> a
}

noeq 
type resource = { 
    t:Type0;
    view:view_t t
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

// Separating conjunction of two resources (TODO: resource fp need to be extended to properly capture empty_resource).
let xor a b = (a || b) && ((not a) || (not b))

let (<*>) (r0 r1:resource) : resource = 
  let t = r0.t & r1.t in
  let fp = None in 
  let inv h = r0.view.inv h /\ r1.view.inv h /\
              Some? r0.view.fp /\ Some? r1.view.fp /\
              xor (Some?.v r0.view.fp) (Some?.v r0.view.fp)
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
let imem inv = h:mem{inv h}

let rst_w (a:Type) (r:resource) = (a -> imem r.view.inv -> prop) -> imem r.view.inv -> prop

let rst (a:Type) (r:resource) (wp:rst_w a r) =
  d a (fun p h -> 
         r.view.inv h /\ 
         wp (fun x h' -> r.view.inv h' ==> p x h') h)

// The RST effect comes with expected operations.
let return (#a:Type) (#r:resource) (x:a) : rst a r (fun p h -> p x h) =
  Ret x

// TODO: implement bind, restrict WPs to monotonic predicate transformers

let get b : rst nat (loc_resource b) (fun p h -> p (h b) h) =
  Get b (fun n -> Ret n)

let put b n : rst unit (loc_resource b) (fun p h -> p () (fun b' -> if b = b' then n else h b')) =
  assert_norm (theta (Put b n (Ret ())) == (fun p h -> p () (fun b' -> if b = b' then n else h b')));
  Put b n (Ret ())

// Parallel composition that splits resources up between the two threads.
let par (#a #b:Type) 
        (#r0 #r1:resource) 
        (#wp0:rst_w a r0)
        (#wp1:rst_w b r1)
        (c0:rst a r0 wp0)
        (c1:rst b r1 wp1)
      : rst (a & b) (r0 <*> r1) (fun p h -> wp0 p h /\ wp1 p h) =
  m_par c0 c1

let (<||>) (#a #b:Type) 
           (#r0 #r1:resource) 
           (#wp0:rst_w a r0)
           (#wp1:rst_w b r1)
           (c0:rst a r0 wp0)
           (c1:rst b r1 wp1) = 
  par c0 c1

// Parallel composition based on G. Plotkin's reformulated definition.
let par' (#r0 #r1:resource) 
        (#wp0:rst_w unit r0)
        (#wp1:rst_w unit r1)
        (c0:rst unit r0 wp0)
        (c1:rst unit r1 wp1)
      : rst unit (r0 <*> r1) (fun p h -> wp0 p h /\ wp1 p h) =
  m_par' c0 c1
