module Sec2.IFC

(* Information-flow control as a plain state monad.
   The old layered effect has been removed; the labels and flow set are now
   ordinary parameters of the computation representation. *)

open FStar.List.Tot
open FStar.Map
open FStar.Set

let loc = int
type store = m:Map.t loc int{forall l. contains m l}
let upd (s:store) (l:loc) (x:int) : store = Map.upd s l x
let sel (s:store) (l:loc) : int = Map.sel s l

let label = Set.set loc
let label_inclusion (l0 l1:label) = Set.subset l0 l1
let bot : label = Set.empty
let single (l:loc) : label = Set.singleton l
let union (l0 l1:label) = Set.union l0 l1
let is_empty #a (s:Set.set a) = forall (x:a). ~ (Set.mem x s)

type comp a = store -> a & store
let havoc s l x = upd s l x

let does_not_read_loc_v #a (f:comp a) (reads:label) (l:loc) (s0:store) v =
  let s0' = havoc s0 l v in
  let x1, s1 = f s0 in
  let x1', s1' = f s0' in
  x1 == x1' /\
  (forall l'. l' <> l ==> sel s1 l' == sel s1' l') /\
  (sel s1 l == sel s1' l \/ (sel s1 l == sel s0 l /\ sel s1' l == sel s0' l))

let does_not_read_loc #a (f:comp a) (reads:label) (l:loc) (s0:store) =
  forall v. does_not_read_loc_v f reads l s0 v
let reads_ok #a (f:comp a) (reads:label) =
  forall (l:loc) (s:store). ~(Set.mem l reads) ==> does_not_read_loc f reads l s
let writes_ok #a (f:comp a) (writes:Set.set loc) =
  forall (l:loc). ~(Set.mem l writes) ==>
    (forall (s0:store). let _, s0' = f s0 in sel s0 l == sel s0' l)

let flow = label & label
let flows = list flow
let add_source (r:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> union r r0, w0) fs
let add_sink (w:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> r0, union w w0) fs
let has_flow_1 (from to:loc) (f:flow) = from `Set.mem` fst f /\ to `Set.mem` snd f
let has_flow (from to:loc) (fs:flows) = exists rs. rs `List.Tot.memP` fs /\ has_flow_1 from to rs
let flows_included_in (fs0 fs1:flows) =
  forall f0. f0 `List.Tot.memP` fs0 ==>
    (forall from to. has_flow_1 from to f0 /\ from <> to ==> exists f1. f1 `List.Tot.memP` fs1 /\ has_flow_1 from to f1)
let flows_equiv (fs0 fs1:flows) = fs0 `flows_included_in` fs1 /\ fs1 `flows_included_in` fs0

let no_leakage_k #a (f:comp a) (from to:loc) (k:int) =
  forall s0.{:pattern (havoc s0 from k)} sel (snd (f s0)) to == sel (snd (f (havoc s0 from k))) to
let no_leakage #a (f:comp a) (from to:loc) = forall k. no_leakage_k f from to k
let respects_flows #a (f:comp a) (fs:flows) =
  forall from to. {:pattern (no_leakage f from to)} ~(has_flow from to fs) /\ from<>to ==> no_leakage f from to

(* The old effect indices are plain parameters. The representation is the
   underlying state monad; the predicates above state the intended IFC facts. *)
type ist (a:Type) (writes:label) (reads:label) (fs:flows) = comp a

let iread (l:loc) : ist int bot (single l) [] = fun s -> sel s l, s
let return (#a:Type) (#w #r:label) (#fs:flows) (x:a) : ist a w r fs = fun s -> x, s
let iwrite (l:loc) (x:int) : ist unit (single l) bot [] = fun s -> (), upd s l x

let bind (#a #b:Type) (#w0 #r0 #w1 #r1:label) (#fs0 #fs1:flows)
  (x:ist a w0 r0 fs0) (y: a -> ist b w1 r1 fs1)
  : ist b (union w0 w1) (union r0 r1) (fs0 @ add_source r0 ((bot, w1)::fs1)) =
  fun s0 -> let v, s1 = x s0 in y v s1

let (let!) #a #b #w0 #r0 #w1 #r1 #fs0 #fs1
  (x:ist a w0 r0 fs0) (y:a -> ist b w1 r1 fs1)
  : ist b (union w0 w1) (union r0 r1) (fs0 @ add_source r0 ((bot, w1)::fs1)) = bind x y

let read = iread
let write = iwrite

let ref (l:label) = r:loc {r `Set.mem` l}
assume val high : label
let low : label = Set.complement high
let lref = ref low
let href = ref high

let test (l:lref) (h:href)
  : ist unit (union bot (single h)) (union (single l) bot) (add_source (single l) [bot, single h]) =
  let! x = read l in write h x

let test2 (l:lref) (h:href) : ist unit (single h) (single l) [single l, single h] =
  let! x = read l in write h x

let test3 (l:lref) (h:href) : ist unit (single h) (single l) [single l, single h] =
  let! x = read l in write h x

let test3_lab (l:lref) (h:href) : ist unit high low [low, high] =
  let! x = read l in write h x

let test3_1 (l:lref) (h:href) (x:int) : ist int (single h) (single l) [] =
  let! _ = write h 0 in read l

let test4 (l:lref) (h:href) (x:int) : ist int (single l) (single h) [single h, bot] =
  let! _ = write l x in read h

let test5 (l:lref) (h:href) (x:int) : ist int (single l) (single h) [] =
  let! _ = write l x in read h

let test6 (l:lref) (h:href) : ist unit high low [low, high] =
  let! x = read l in write h x

// This leaks the contents of the href.
let test7 (l:lref) (h:href) : ist unit (single l) (single h) [high, low] =
  let! x = read h in write l x

// Label-based IFC is intentionally imprecise for these examples.
let test8 (l:lref) (h:href)
  : ist unit (single l) (union (single h) (single l)) [(single l `union` single h, single l)] =
  let! _ = read h in let! x = read l in write l x

let test9 (l:lref) (h:href)
  : ist unit (single l) (union (single h) (single l)) [(single l `union` single h, single l)] =
  let! x = (let! _ = read h in read l) in write l x

assume val cw0 : label
assume val cr0 : label
assume val c0 : unit -> ist unit cw0 cr0 []
assume val cw1 : label
assume val cr1 : label
assume val c1 : unit -> ist unit cw1 cr1 []
assume val cw2 : label
assume val cr2 : label
assume val c2 : unit -> ist unit cw2 cr2 []

let test10 ()
  : ist unit (union cw0 (union cw1 cw2)) (union cr0 (union cr1 cr2))
        (add_source cr0 ((bot, union cw1 cw2)::(add_source cr1 [bot, cw2]))) =
  let! _ = c0 () in let! _ = c1 () in c2 ()

let test12 ()
  : ist unit (union cw0 (union cw1 cw2)) (union cr0 (union cr1 cr2))
        [(cr0, union cw1 cw2); (union cr0 cr1, cw2)] =
  let! _ = c0 () in let! _ = c1 () in c2 ()

let test12_1 ()
  : ist unit (union cw0 (union cw1 cw2)) (union cr0 (union cr1 cr2))
        [(cr0, cw1); (union cr0 cr1, cw2)] =
  let! _ = c0 () in let! _ = c1 () in c2 ()

let test13 ()
  : ist unit (union (union cw0 cw1) cw2) (union (union cr0 cr1) cr2)
        (add_source cr0 [bot, cw1] @ add_source (union cr0 cr1) [bot, cw2]) =
  let! _ = (let! _ = c0 () in c1 ()) in c2 ()

let test14 ()
  : ist unit (union (union cw0 cw1) cw2) (union (union cr0 cr1) cr2)
        [cr0, cw1; union cr0 cr1, cw2] =
  let! _ = (let! _ = c0 () in c1 ()) in c2 ()

let test15 (l:lref) : ist unit (single l) (single l) [] =
  let! x = read l in write l x
