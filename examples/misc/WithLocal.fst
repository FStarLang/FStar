module WithLocal
module B = LowStar.Buffer
module HS = FStar.HyperStack
open FStar.HyperStack.ST

let eloc = Ghost.erased B.loc

let loc_buf (x:B.pointer 'a)
  : Ghost.erased B.loc
  = B.loc_buffer x

let frameable (l:Ghost.erased B.loc) (p:HS.mem -> Type) =
    forall h0 h1 l'.
      p h0 /\
      B.loc_disjoint l l' /\
      B.modifies l' h0 h1
      ==> p h1

let hprop (l:Ghost.erased B.loc) =
  p:(HS.mem -> Type) { frameable l p }

let hpost (#a:Type) (l:a -> Ghost.erased B.loc) =
  p:(HS.mem -> a -> HS.mem -> Type) {
    forall h0 x. frameable (l x) (p h0 x)
  }

let stl (a:Type) #b (v:b) (l1:Ghost.erased B.loc) (l2: a -> Ghost.erased B.loc) (req:hprop l1) (ens:hpost l2) =
    hinit:HS.mem ->
    fresh:B.pointer b ->
    ST a
    (requires fun h ->
      B.modifies B.loc_none hinit h /\
      B.loc_disjoint (B.loc_addr_of_buffer fresh) l1 /\
      B.live h fresh /\
      B.get h fresh 0 == v /\
      req hinit)
    (ensures fun h0 x h1 ->
      B.live h1 fresh /\
      B.loc_disjoint (B.loc_addr_of_buffer fresh) (l2 x) /\
      B.modifies (B.loc_union (B.loc_buffer fresh) (l2 x)) h0 h1 /\
      ens hinit x h1)

let with_local
      (#a:Type)
      (#b:Type)
      (#l1:_)
      (#l2:_)
      (#req: hprop l1)
      (#ens: hpost l2)
      (init:b)
      (f: stl a init l1 l2 req ens)
  : ST a
    (requires fun h ->
       B.loc_includes (B.loc_not_unused_in h) l1 /\
       req h)
    (ensures fun h0 x h1 ->
       B.modifies (l2 x) h0 h1 /\
       ens h0 x h1)
  = let h = get () in
    B.loc_unused_in_not_unused_in_disjoint h;
    let fresh = B.malloc HS.root init 1ul in
    let h1 = get () in
    let res = f h fresh in
    let h2 = get () in
    let _ = B.free fresh in
    let h3 = get () in
    B.modifies_remove_new_locs (B.loc_addr_of_buffer fresh) (l2 res) (l2 res) h h1 h3;
    res


val test (x:B.pointer int)
  : stl unit 1 (loc_buf x) (fun _ -> loc_buf x)
    (fun h ->
        B.live h x /\
        B.get h x 0 > 17)
    (fun h0 _ h1 ->
        B.live h1 x /\
        B.get h1 x 0 >
        B.get h0 x 0)
let test x hinit fresh =
  let v = B.index fresh 0ul in
  let y = B.index x 0ul in
  B.upd x 0ul (y + y)

let use_test (x:B.pointer int)
  : ST unit
    (requires fun h ->
      B.live h x /\
      B.get h x 0 > 17)
    (ensures fun h0 _ h1 ->
      B.live h1 x /\
      B.get h1 x 0 > B.get h0 x 0 /\
      B.modifies (B.loc_buffer x) h0 h1)
  = with_local 1 (test x)
