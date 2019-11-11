module Memory
open FStar.Real
let frac = r:FStar.Real.real{FStar.Real.(0.0R <. r && r <=. 1.0R)}

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell =
  | Ref : a:Type ->
          v:a ->
          perm:frac ->
          cell

let addr = nat

let mem : Type u#(a + 1) = addr -> option (cell u#a)

let contains_addr (m:mem) (a:addr)
  : bool
  = Some? (m a)

let select_addr (m:mem) (a:addr{contains_addr m a})
  : cell
  = Some?.v (m a)

let update_addr (m:mem) (a:addr) (c:cell)
  : mem
  = fun a' -> if a = a' then Some c else m a

let disjoint (m0 m1:mem)
  : prop
  = forall a. match m0 a, m1 a with
         | Some (Ref t0 v0 p0), Some (Ref t1 v1 p1) ->
           p0 +. p1 <. 1.0R /\
           t0 == t1 /\
           v0 == v1

         | Some _, None
         | None, Some _ ->
           True

         | _ ->
           False

let join (m0:mem) (m1:mem{disjoint m0 m1})
  : mem
  = fun a ->
      if contains_addr m0 a
      then m0 a
      else m1 a

////////////////////////////////////////////////////////////////////////////////

let ref (a:Type) = addr

module W = FStar.WellFounded

noeq
type hprop =
  | Pts_to : #a:_ -> r:ref a -> perm:frac -> v:a -> hprop
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
      (let Ref a' v' perm' = select_addr m r in
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

let equiv (p1 p2:hprop) = forall m. interp p1 m <==> interp p2 m

let hmem (p:hprop) = m:mem{interp p m}

let ptr_perm #a (r:ref a) (p:frac) =
    Ex (fun v -> Pts_to r p v)

let ptr #a (r:ref a) =
    Ex (fun p -> ptr_perm r p)

let sel #a (r:ref a) (m:hmem (ptr r))
  : a
  = let Ref _ v _ = select_addr m r in
    v

let sel_lemma #a (r:ref a) (p:frac) (m:hmem (ptr_perm r p))
  : Lemma (let v = sel r m in
           interp (Pts_to r p v) m)
  = ()

let upd #a (r:ref a) (v:a) (m:hmem (ptr r))
  : mem
  = let Ref _ _ p = select_addr m r in
    update_addr m r (Ref a v p)

(* Alternatively:

let upd' #a (r:ref a) (v:a)
            (frame:hprop) (m:hmem (ptr_perm r 1.0R  `Star` frame))
  : m:hmem (Pts_to r 1.0R v `Star` frame)
  = let m0, m1 = FStar.IndefiniteDescription.indefinitedescription ... in
    join (upd m0 ...) m1

*)

let upd_lemma #a (r:ref a) (v:a) (m:hmem (ptr r))
  : Lemma (let m' = upd r v m in
           interp (Ex (fun p -> Pts_to r p v)) m')
  = ()

let upd_star #a0 (r0:ref a0) (p0:frac) (v0:a0)
             #a1 (r1:ref a1) (p1:frac{p0 +. p1 >. 1.0R}) (v1:a1)
             (m:hmem (Pts_to r0 p0 v0 `Star` Pts_to r1 p1 v1))
  : Lemma (let m' = upd r0 v0 m in
           interp (Ex (fun p -> Pts_to r0 p v0) `Star` Pts_to r1 p1 v1) m')
  = let m' = upd r0 v0 m in
    assert (interp (Ex (fun p -> Pts_to r0 p v0)) m');
    let aux (m0 m1:mem)
       : Lemma
         (requires
           p0 +. p1 >. 1.0R /\
           interp (Pts_to r0 p0 v0) m0 /\
           interp (Pts_to r1 p1 v1) m1 /\
           disjoint m0 m1 /\
           m == join m0 m1)
         (ensures interp (Ex (fun p -> Pts_to r0 p v0) `Star` Pts_to r1 p1 v1) m')
         [SMTPat (interp (Pts_to r0 p0 v0) m0);
          SMTPat (interp (Pts_to r1 p1 v1) m1)]
       = assert (interp (Ex (fun p -> Pts_to r0 p v0)) m');
         assert (r0 <> r1);
         assume (interp (Pts_to r1 p1 v1) m);
         assert (sel r1 m == v1);
         let Ref _ _ p = select_addr m r0 in
         assert (m' == update_addr m r0 (Ref a0 v0 p));
         assume ((update_addr m r0 (Ref a0 v0 p)) r1 == m r1);
         assert (sel r1 m' == v1);
         assert (exists p1'. p1' >=. p1 /\ select_addr m' r1 == Ref a1 v1 p1');
         assert (interp (Pts_to r1 p1 v1) m');
         assert (interp (Pts_to r0 p0 v0) m');
         assume (interp (Pts_to r0 p0 v0 `Star` Pts_to r1 p1 v1) m')
    in
    assert (exists m0 m1.
              disjoint m0 m1 /\
              m == join m0 m1 /\
              interp (Pts_to r0 p0 v0) m0 /\
              interp (Pts_to r1 p1 v1) m1)
