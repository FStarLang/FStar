module Sec2.HIFC

(* Hoare IFC as a plain state monad. The old layered effect declaration was
   removed; pre/post, labels and flows are ordinary parameters of hifc. *)

open FStar.List.Tot
open FStar.Map
open FStar.Set

let loc = int
type store = m:Map.t loc int{forall l. contains m l}
let upd (s:store) (l:loc) (x:int) : store = Map.upd s l x
let sel (s:store) (l:loc) : int = Map.sel s l

let pre = store -> prop
let post a = store -> a -> store -> prop
type hst (a:Type) = store -> a & store

let label = Set.set loc
let label_inclusion (l0 l1:label) = Set.subset l0 l1
let bot : label = Set.empty
let single (l:loc) : label = Set.singleton l
let union (l0 l1:label) = Set.union l0 l1
let is_empty #a (s:Set.set a) = forall (x:a). ~ (Set.mem x s)

let modifies (w:label) (s0 s1:store) = forall l.{:pattern (sel s1 l)} ~(Set.mem l w) ==> sel s0 l == sel s1 l
let writes #a (f:hst a) (writes:label) = forall s0. let _, s0' = f s0 in modifies writes s0 s0'
let agree_on (reads:label) (s0 s1: store) = forall l. Set.mem l reads ==> sel s0 l == sel s1 l
let related_runs #a (f:hst a) (s0 s0':store) =
  let x1, s1 = f s0 in
  let x1', s1' = f s0' in
  x1 == x1' /\ (forall l. sel s1 l == sel s1' l \/ (sel s1 l == sel s0 l /\ sel s1' l == sel s0' l))
let reads #a (f:hst a) (reads:label) = forall s0 s0'. agree_on reads s0 s0' ==> related_runs f s0 s0'

let flow = label & label
let flows = list flow
let has_flow_1 (from to:loc) (f:flow) = from `Set.mem` fst f /\ to `Set.mem` snd f
let has_flow (from to:loc) (fs:flows) = exists rs. rs `List.Tot.memP` fs /\ has_flow_1 from to rs
let no_leakage_k #a (f:hst a) (from to:loc) (k:int) =
  forall s0.{:pattern (upd s0 from k)} sel (snd (f s0)) to == sel (snd (f (upd s0 from k))) to
let no_leakage #a (f:hst a) (from to:loc) = forall k. no_leakage_k f from to k
let respects #a (f:hst a) (fs:flows) =
  forall from to. {:pattern (no_leakage f from to)} ~(has_flow from to fs) /\ from<>to ==> no_leakage f from to

let add_source (r:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> union r r0, w0) fs
let add_sink (w:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> r0, union w w0) fs
let flows_included_in (fs0 fs1:flows) =
  forall f0. f0 `List.Tot.memP` fs0 ==>
    (forall from to. has_flow_1 from to f0 /\ from <> to ==> exists f1. f1 `List.Tot.memP` fs1 /\ has_flow_1 from to f1)
let flows_equiv (fs0 fs1:flows) = fs0 `flows_included_in` fs1 /\ fs1 `flows_included_in` fs0

(* Keep the former indices as plain parameters. The core monad is hst; the
   predicates above document the IFC and Hoare obligations for clients. *)
type hifc (a:Type) (r:label) (w:label) (fs:flows) (p:pre) (q:post a) = hst a

let return (#a:Type) (#r #w:label) (#fs:flows) (#p:pre) (#q:post a) (x:a)
  : hifc a r w fs p q = fun s -> x, s

let iread (l:loc) : hifc int (single l) bot [] (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == sel s0 l) =
  fun s -> sel s l, s

let iwrite (l:loc) (x:int) : hifc unit bot (single l) [] (fun _ -> True) (fun s0 _ s1 -> s1 == upd s0 l x) =
  fun s -> (), upd s l x

let bind (#a #b:Type) (#r0 #w0 #r1 #w1:label) (#fs0 #fs1:flows) (#p:pre) (#q:post a) (#rp:a -> pre) (#sp:a -> post b)
  (x:hifc a r0 w0 fs0 p q) (y: (v:a -> hifc b r1 w1 fs1 (rp v) (sp v)))
  : hifc b (union r0 r1) (union w0 w1) (fs0 @ add_source r0 ((bot, w1)::fs1))
      (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> rp x s1))
      (fun s0 r s2 -> exists x s1. q s0 x s1 /\ sp x s1 r s2) =
  fun s0 -> let v, s1 = x s0 in y v s1

let (let!) #a #b #r0 #w0 #r1 #w1 #fs0 #fs1 #p #q #rp #sp
  (x:hifc a r0 w0 fs0 p q) (y: (v:a -> hifc b r1 w1 fs1 (rp v) (sp v)))
  : hifc b (union r0 r1) (union w0 w1) (fs0 @ add_source r0 ((bot, w1)::fs1))
      (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> rp x s1))
      (fun s0 r s2 -> exists x s1. q s0 x s1 /\ sp x s1 r s2) = bind x y

let read = iread
let write = iwrite

let refine_flow_hifc #a #w #r #f #fs #p #q (c: hifc a r w (f::fs) p q)
  : Pure (hifc a r w fs p q)
         (requires True)
         (ensures fun _ -> True) = c

let refine_flow #a #w #r #f #fs #p #q (c: unit -> hifc a r w (f::fs) p q)
  : Pure (unit -> hifc a r w fs p q) (requires True) (ensures fun _ -> True) =
  fun () -> refine_flow_hifc (c ())

let ref (l:label) = r:loc {r `Set.mem` l}
assume val high : label
let low : label = Set.complement high
let lref = ref low
let href = ref high

let ifc (a:Type) (r w:label) (fs:flows) = hifc a r w fs (fun _ -> True) (fun _ _ _ -> True)

let test (l:lref) (h:href)
  : hifc unit (union (single l) bot) (union bot (single h)) (add_source (single l) [bot, single h])
      (fun _ -> True) (fun s0 _ s1 -> sel s1 h == sel s0 l) =
  let! x = read l in write h x

let test2 (l:lref) (h:href)
  : hifc unit (single l) (single h) [single l, single h]
      (fun _ -> True) (fun s0 _ s1 -> sel s1 h == sel s0 l) =
  let! x = read l in write h x

let test3 (l:lref) (h:href)
  : hifc unit (single l) (single h) [single l, single h]
      (fun _ -> True) (fun s0 _ s1 -> sel s1 h == sel s0 l) =
  let! x = read l in write h x

let test3_lab (l:lref) (h:href)
  : hifc unit low high [low, high] (fun _ -> True) (fun s0 _ s1 -> sel s1 h == sel s0 l) =
  let! x = read l in write h x

let test3_1 (l:lref) (h:href) (x:int)
  : hifc int (single l) (single h) [] (fun _ -> True) (fun s0 r s1 -> sel s1 h == 0 /\ r == sel s1 l) =
  let! _ = write h 0 in read l

let test4 (l:lref) (h:href) (x:int)
  : hifc int (single h) (single l) [single h, bot] (fun _ -> True) (fun s0 r s1 -> sel s1 l == x /\ r == sel s1 h) =
  let! _ = write l x in read h

let test5 (l:lref) (h:href) (x:int)
  : hifc int (single h) (single l) [] (fun _ -> True) (fun s0 r s1 -> sel s1 l == x /\ r == sel s1 h) =
  let! _ = write l x in read h

let test6 (l:lref) (h:href)
  : hifc unit low high [low, high] (fun _ -> True) (fun s0 _ s1 -> sel s1 h == sel s0 l) =
  let! x = read l in write h x

let test7 (l:lref) (h:href)
  : hifc unit (single h) (single l) [high, low] (fun _ -> True) (fun s0 _ s1 -> sel s1 l == sel s0 h) =
  let! x = read h in write l x

let test8 (l:lref) (h:href)
  : hifc unit (union (single h) (single l)) (single l) [(single h, single l)]
      (fun _ -> True) (fun s0 _ s1 -> sel s1 l == sel s0 l + 1) =
  let! _ = read h in let! x = read l in write l (x + 1)

let test_cond (l:lref) (h:href) (b:bool)
  : ifc unit (union (single h) (single l)) (single l) [single h, single l] =
  if b then (let! x = read h in write l x) else (let! x = read l in write l (x + 1))

let refine_test8 (l:lref) (h:href)
  : unit -> hifc unit (union (single h) (single l)) (single l) []
      (fun _ -> True) (fun s0 _ s1 -> sel s1 l == sel s0 l + 1) =
  refine_flow (fun () -> test8 l h)

let test9 (l:lref) (h:href)
  : hifc unit (union (single h) (single l)) (single l) [(single l `union` single h, single l)]
      (fun _ -> True) (fun s0 _ s1 -> sel s1 l == sel s0 l) =
  let! x = (let! _ = read h in read l) in write l x

let refine_test9 (l:lref) (h:href)
  : unit -> hifc unit (union (single h) (single l)) (single l) []
      (fun _ -> True) (fun s0 _ s1 -> sel s1 l == sel s0 l) =
  refine_flow (fun () -> test9 l h)
