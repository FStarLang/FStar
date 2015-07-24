
type sidt =
Prims.nat

type memblock =
Prims.heap

type memStackAux =
(sidt, memblock) Prims.l__Tuple2 Stack.l__Stack

let ssids = (fun ( ms  :  memStackAux ) -> (List.mapT () Prims.fst ms))

let wellFormed = (fun ( ms  :  memStackAux ) -> (ListSet.noRepeats () (ssids ms)))

type memStack =
memStackAux

type smem =
(memblock, memStack) Prims.l__Tuple2

let hp = (fun ( s  :  smem ) -> (Prims.fst () s))

let st = (fun ( s  :  smem ) -> (Prims.snd () s))

let mtail = (fun ( s  :  smem ) -> Prims.MkTuple2 ((), (hp s), (Stack.stail () (st s))))

let mstail = (fun ( s  :  smem ) -> (Stack.stail () (st s)))

let sids = (fun ( m  :  smem ) -> (ssids (st m)))

let sid = (fun ( s  :  (sidt, memblock) Prims.l__Tuple2 ) -> (Prims.fst () s))

let topst = (fun ( ss  :  smem ) -> (Stack.top () (st ss)))

let topstb = (fun ( ss  :  smem ) -> (Prims.snd () (topst ss)))

let topstid = (fun ( ss  :  smem ) -> (Prims.fst () (topst ss)))

type refLocType =
| InHeap
| InStack of sidt

let is_InHeap = (fun ( _discr_ ) -> (match (_discr_) with
| InHeap (_) -> begin
true
end
| _ -> begin
false
end))

let is_InStack = (fun ( _discr_ ) -> (match (_discr_) with
| InStack (_) -> begin
true
end
| _ -> begin
false
end))

let refLoc = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let rec stackBlockAtLoc = (fun ( id  :  sidt ) ( sp  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> (match (sp) with
| Nil -> begin
l__None
end
| Cons (h, tl) -> begin
(match ((Prims.op_Equality () id (Prims.fst () h))) with
| true -> begin
Some ((), (Prims.snd () h))
end
| false -> begin
(stackBlockAtLoc id tl)
end)
end))

let blockAtLoc = (fun ( m  :  smem ) ( rl  :  refLocType ) -> (match (rl) with
| InHeap -> begin
Some ((), (hp m))
end
| InStack (id) -> begin
(stackBlockAtLoc id (st m))
end))

let writeInBlock = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( v  :  'a ) ( mb  :  memblock ) -> (Heap.upd () mb r v))

let rec changeStackBlockWithId = (fun ( f  :  memblock  ->  memblock ) ( s  :  sidt ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> (match (ms) with
| Nil -> begin
l__Nil
end
| Cons (h, tl) -> begin
(match ((Prims.op_Equality () (Prims.fst () h) s)) with
| true -> begin
Cons ((), Prims.MkTuple2 ((), (Prims.fst () h), (f (Prims.snd () h))), tl)
end
| false -> begin
Cons ((), h, (changeStackBlockWithId f s tl))
end)
end))

let rec writeInMemStack = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) ( s  :  sidt ) ( v  :  'a ) -> (changeStackBlockWithId (writeInBlock () r v) s ms))

let rec changeStackBlockSameIDs = (fun ( f  :  memblock  ->  memblock ) ( s  :  sidt ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> ())

let changeStackBlockWellFormed = (fun ( f  :  memblock  ->  memblock ) ( s  :  sidt ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> ())

let writeMemStackSameIDs = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) ( s  :  sidt ) ( v  :  'a ) -> ())

let writeMemStackWellFormed = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) ( s  :  sidt ) ( v  :  'a ) -> ())

let rec refExistsInStack = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( id  :  sidt ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> (match (ms) with
| Nil -> begin
false
end
| Cons (h, tl) -> begin
(match ((Prims.op_Equality () (Prims.fst () h) id)) with
| true -> begin
(Heap.contains () (Prims.snd () h) r)
end
| false -> begin
(refExistsInStack () r id tl)
end)
end))

let rec refExistsInStackId = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( id  :  sidt ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> ())

let memIdUniq = (fun ( h  :  (sidt, memblock) Prims.l__Tuple2 ) ( tl  :  memStackAux ) -> ())

let refExistsInStackTail = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( id  :  sidt ) ( ms  :  memStack ) -> ())

let refExistsInMem = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( m  :  smem ) -> (match ((refLoc () r)) with
| InHeap -> begin
(Heap.contains () (hp m) r)
end
| InStack (id) -> begin
(refExistsInStack () r id (st m))
end))

let rec writeMemStackExists = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'b Prims.ref ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) ( id  :  sidt ) ( idw  :  sidt ) ( v  :  'a ) -> ())

let writeMemAux = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( m  :  smem ) ( v  :  'a ) -> (match ((refLoc () r)) with
| InHeap -> begin
Prims.MkTuple2 ((), (Heap.upd () (hp m) r v), (Prims.snd () m))
end
| InStack (id) -> begin
Prims.MkTuple2 ((), (hp m), (writeInMemStack () r (st m) id v))
end))

let writeMemAuxPreservesExists = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'b Prims.ref ) ( m  :  smem ) ( v  :  'a ) -> ())

let writeMemAuxPreservesSids = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( m  :  smem ) ( v  :  'a ) -> ())

let rec loopkupRefStack = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( id  :  sidt ) ( ms  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> (match (ms) with
| Cons (h, tl) -> begin
(match ((Prims.op_Equality () (Prims.fst () h) id)) with
| true -> begin
(Heap.sel () (Prims.snd () h) r)
end
| false -> begin
(loopkupRefStack () r id tl)
end)
end))

let loopkupRef = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( m  :  smem ) -> (match ((refLoc () r)) with
| InHeap -> begin
(Heap.sel () (hp m) r)
end
| InStack (id) -> begin
(loopkupRefStack () r id (st m))
end))

type ('b, 'tc, 'fc) ifthenelseT =
(('b, 'tc) Prims.l_imp, ('b Prims.l_not, 'fc) Prims.l_imp) Prims.l_and

let rec readAfterWriteStack = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'b Prims.ref ) ( v  :  'a ) ( id  :  sidt ) ( idw  :  sidt ) ( m  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> ())

let readAfterWriteStackSameType = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'a Prims.ref ) ( v  :  'a ) ( id  :  sidt ) ( idw  :  sidt ) ( m  :  (sidt, memblock) Prims.l__Tuple2 Stack.l__Stack ) -> ())

let readAfterWrite = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'b Prims.ref ) ( v  :  'a ) ( m  :  smem ) -> ())

let readAfterWriteTrue = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'b Prims.ref ) ( v  :  'a ) ( m  :  smem ) -> ())

let readAfterWriteFalse = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'b Prims.ref ) ( v  :  'a ) ( m  :  smem ) -> ())

let readAfterWriteSameType = (fun ( _7_16450  :  unit ) ( rw  :  'a Prims.ref ) ( r  :  'a Prims.ref ) ( v  :  'a ) ( m  :  smem ) -> ())

let refExistsInMemTail = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( m  :  smem ) -> ())

let loopkupRefStackTail = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( id  :  sidt ) ( ms  :  memStack ) -> ())

let readTailRef = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( m  :  smem ) -> ())

let writeStackTail = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( id  :  sidt ) ( v  :  'a ) ( ms  :  memStack ) -> ())

let writeTailRef = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( m  :  smem ) ( v  :  'a ) -> ())

let refExistsInMemSTailSids = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( id  :  sidt ) ( m0  :  memStack ) ( m1  :  memStack ) -> ())

let refExistsInMemTailSids = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( m0  :  smem ) ( m1  :  smem ) -> ())

type ('m0, 'm1, 'rs) canModify =
(Obj.t Prims.ref, (unit Prims.b2t, (unit Prims.b2t Prims.l_not, (unit Prims.b2t, unit Prims.b2t) Prims.l_and) Prims.l_imp) Prims.l_imp) Prims.l__Forall Prims.l__ForallTyp

type ('a, 'r, 'v, 'm) mreads =
(unit Prims.b2t, unit Prims.b2t) Prims.l_and

let canModifyNone = (fun ( m  :  smem ) -> ())

let canModifyWrite = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( v  :  'a ) ( m  :  smem ) -> ())

type ('a, 'r, 'h0, 'h1, 'init) allocateInBlock =
((unit Prims.b2t, unit Prims.b2t) Prims.l_and, (memblock, Prims.heap, unit, unit) Prims.l__Eq2) Prims.l_and

let halloc = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let salloc = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let memread = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let memwrite = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let pushStackFrame = (failwith () "Not yet implemented")

let popStackFrame = (failwith () "Not yet implemented")

type 'm mStackNonEmpty =
unit Prims.b2t

let allRefs = (Set.complement () Set.empty)

let withNewScope = (fun ( _7_16450  :  unit ) ( mods  :  Heap.aref Set.set ) ( body  :  unit  ->  'a ) -> (let _7_457 = (pushStackFrame ())
in (let v = (body ())
in (let _7_460 = (popStackFrame ())
in v))))

let rec scopedWhile = (fun ( _7_16450  :  unit ) ( wg  :  unit  ->  'loopInv ) ( mods  :  Heap.aref Set.set ) ( bd  :  unit  ->  'loopInv ) -> (match ((wg ())) with
| true -> begin
(let _7_499 = (withNewScope () mods (Obj.magic bd))
in (scopedWhile () wg mods bd))
end
| false -> begin
()
end))

let scopedWhile1 = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( lc  :  'a  ->  Prims.bool ) ( 'loopInv  :  unit ) ( mods  :  Heap.aref Set.set ) ( bd  :  unit  ->  (Obj.t, unit Prims.b2t) Prims.l_and ) -> (scopedWhile () (Obj.magic (fun ( u  :  unit ) -> (let _7_18838 = (memread () r)
in (lc _7_18838)))) mods bd))

let scopedWhile2 = (fun ( _7_16450  :  unit ) ( ra  :  'a Prims.ref ) ( rb  :  'b Prims.ref ) ( lc  :  'a  ->  'b  ->  Prims.bool ) ( 'loopInv  :  unit ) ( mods  :  Heap.aref Set.set ) ( bd  :  unit  ->  ((Obj.t, unit Prims.b2t) Prims.l_and, unit Prims.b2t) Prims.l_and ) -> (scopedWhile () (Obj.magic (fun ( u  :  unit ) -> (let _7_18878 = (memread () ra)
in (let _7_18877 = (memread () rb)
in (lc _7_18878 _7_18877))))) mods bd))




