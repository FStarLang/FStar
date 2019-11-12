module Memory
open FStar.Real
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
let perm = r:FStar.Real.real{FStar.Real.(0.0R <. r && r <=. 1.0R)}

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell =
  | Ref : a:Type ->
          perm:perm ->
          v:a ->
          cell

let addr = nat

let mem : Type u#(a + 1) = addr ^-> option (cell u#a)

let contains_addr (m:mem) (a:addr)
  : bool
  = Some? (m a)

let select_addr (m:mem) (a:addr{contains_addr m a})
  : cell
  = Some?.v (m a)

let update_addr (m:mem) (a:addr) (c:cell)
  : mem
  = F.on _ (fun a' -> if a = a' then Some c else m a')

module T = FStar.Tactics


let disjoint_addr (m0 m1:mem) (a:addr)
  : prop
  = match m0 a, m1 a with
    | Some (Ref t0 p0 v0), Some (Ref t1 p1 v1) ->
      p0 +. p1 <=. 1.0R /\
      t0 == t1 /\
      v0 == v1

    | Some _, None
    | None, Some _
    | None, None ->
      True

    | _ ->
      False

let disjoint (m0 m1:mem)
  : prop
  = forall a. disjoint_addr m0 m1 a

let join (m0:mem) (m1:mem{disjoint m0 m1})
  : mem
  = F.on _ (fun a ->
      match m0 a, m1 a with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some (Ref a0 p0 v0), Some (Ref a1 p1 v1) ->
        Some (Ref a0 (p0 +. p1) v0))

////////////////////////////////////////////////////////////////////////////////

let ref (a:Type) = addr

module W = FStar.WellFounded

noeq
type hprop =
  | Pts_to : #a:_ -> r:ref a -> perm:perm -> v:a -> hprop
  | And  : hprop -> hprop -> hprop
  | Or   : hprop -> hprop -> hprop
  | Star : hprop -> hprop -> hprop
  | Wand : hprop -> hprop -> hprop
  | Ex   : #a:_ -> (a -> hprop) -> hprop
  | All  : #a:_ -> (a -> hprop) -> hprop

let rec interp (p:hprop) (m:mem)
  : Tot prop (decreases p)
  = match p with
    | Pts_to #a r perm v ->
      m `contains_addr` r /\
      (let Ref a' perm' v' = select_addr m r in
       a == a' /\
       v == v' /\
       perm <=. perm')

    | And p1 p2 ->
      interp p1 m /\
      interp p2 m

    | Or  p1 p2 ->
      interp p1 m \/
      interp p2 m

    | Star p1 p2 ->
      exists m1 m2.
        m1 `disjoint` m2 /\
        m == join m1 m2 /\
        interp p1 m1 /\
        interp p2 m2

    | Wand p1 p2 ->
      forall m1.
        m `disjoint` m1 /\
        interp p1 m1 ==>
        interp p2 (join m m1)

    | Ex f ->
      exists x. (W.axiom1 f x; interp (f x) m)

    | All f ->
      forall x. (W.axiom1 f x; interp (f x) m)

let equiv (p1 p2:hprop) =
  forall m. interp p1 m <==> interp p2 m

let hmem (p:hprop) = m:mem{interp p m}

let ptr_perm #a (r:ref a) (p:perm) =
    Ex (fun v -> Pts_to r p v)

let ptr #a (r:ref a) =
    Ex (fun p -> ptr_perm r p)

let sel #a (r:ref a) (m:hmem (ptr r))
  : a
  = let Ref _ _ v = select_addr m r in
    v

let sel_lemma #a (r:ref a) (p:perm) (m:hmem (ptr_perm r p))
  : Lemma (let v = sel r m in
           interp (Pts_to r p v) m)
  = ()

let split_mem_ghost (p1 p2:hprop) (m:hmem (p1 `Star` p2))
  : GTot (ms:(hmem p1 & hmem p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
  = let open FStar.IndefiniteDescription in
    let (| m1, p |)
      : (m1:mem &
        (exists (m2:mem).
          m1 `disjoint` m2 /\
          m == join m1 m2 /\
          interp p1 m1 /\
          interp p2 m2))
        =
      indefinite_description
        mem
        (fun (m1:mem) ->
          exists (m2:mem).
            m1 `disjoint` m2 /\
            m == join m1 m2 /\
            interp p1 m1 /\
            interp p2 m2)
    in
    let p :
      (exists (m2:mem).
        m1 `disjoint` m2 /\
        m == join m1 m2 /\
        interp p1 m1 /\
        interp p2 m2) = p
    in
    let _ = FStar.Squash.return_squash p in
    let (| m2, _ |) =
      indefinite_description
        mem
        (fun (m2:mem) ->
           m1 `disjoint` m2 /\
           m == join m1 m2 /\
           interp p1 m1 /\
           interp p2 m2)
    in
    (m1, m2)

assume
private
val axiom_ghost_to_tot (#a:Type) (#b:a -> Type) ($f: (x:a -> GTot (b x))) (x:a)
  : Tot (b x)

let split_mem (p1 p2:hprop) (m:hmem (p1 `Star` p2))
  : Tot (ms:(hmem p1 & hmem p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
  = axiom_ghost_to_tot (split_mem_ghost p1 p2) m

let upd #a (r:ref a) (v:a)
           (frame:hprop) (m:hmem (ptr_perm r 1.0R  `Star` frame))
  : Tot (m:hmem (Pts_to r 1.0R v `Star` frame))
  = let m0, m1 = split_mem (ptr_perm r 1.0R) frame m in
    let m0' = update_addr m0 r (Ref a 1.0R v) in
    join m0' m1

let mem_equiv (m0 m1:mem) =
  forall a. m0 a == m1 a

let mem_equiv_eq (m0 m1:mem)
  : Lemma
    (requires
      m0 `mem_equiv` m1)
    (ensures
      m0 == m1)
    [SMTPat (m0 `mem_equiv` m1)]
  = F.extensionality _ _ m0 m1

let join_commutative (m0 m1:mem)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      join m0 m1 `mem_equiv` join m1 m0)
    [SMTPat (join m0 m1)]
  = ()

let join_associative (m0 m1 m2:mem)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      disjoint m0 m1 /\
      disjoint (join m0 m1) m2  /\
      join m0 (join m1 m2) `mem_equiv` join (join m0 m1) m2)
    [SMTPat (join m0 (join m1 m2))]
  = ()

let join_associative2 (m0 m1 m2:mem)
  : Lemma
    (requires
      disjoint m0 m1 /\
      disjoint (join m0 m1) m2)
    (ensures
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) /\
      join m0 (join m1 m2) `mem_equiv` join (join m0 m1) m2)
    [SMTPat (join (join m0 m1) m2)]
  = ()

let star_commutative (p1 p2:hprop)
  : Lemma ((p1 `Star` p2) `equiv` (p2 `Star` p1))
  = ()

#push-options "--query_stats --z3rlimit_factor 4 --max_fuel 2 --initial_fuel 2 --max_ifuel 2 --initial_ifuel 2"
let star_associative (p1 p2 p3:hprop)
  : Lemma ((p1 `Star` (p2 `Star` p3)) `equiv` ((p1 `Star` p2) `Star` p3))
  = ()
#pop-options
