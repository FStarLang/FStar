
type sidt =
Support.Prims.nat

type memblock =
Support.Prims.heap

type memStackAux =
(sidt * memblock) Stack.l__Stack

let ssids = (fun ( ms ) -> (Support.List.mapT Support.Prims.fst ms))

let wellFormed = (fun ( ms ) -> (ListSet.noRepeats (ssids ms)))

type memStack =
memStackAux

type smem =
(memblock * memStack)

let hp = (fun ( s ) -> (Support.Prims.fst s))

let st = (fun ( s ) -> (Support.Prims.snd s))

let mtail = (fun ( s ) -> ((hp s), (Stack.stail (st s))))

let mstail = (fun ( s ) -> (Stack.stail (st s)))

let sids = (fun ( m ) -> (ssids (st m)))

let sid = (fun ( s ) -> (Support.Prims.fst s))

let topst = (fun ( ss ) -> (Stack.top (st ss)))

let topstb = (fun ( ss ) -> (Support.Prims.snd (topst ss)))

let topstid = (fun ( ss ) -> (Support.Prims.fst (topst ss)))

type refLocType =
| InHeap
| InStack of sidt

let is_InHeap = (fun ( _discr_ ) -> (match (_discr_) with
| InHeap -> begin
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

let refLoc = (fun ( _ ) -> (failwith ("Not yet implemented")))

let rec stackBlockAtLoc = (fun ( id ) ( sp ) -> (match (sp) with
| [] -> begin
None
end
| h::tl -> begin
(match ((id = (Support.Prims.fst h))) with
| true -> begin
Some ((Support.Prims.snd h))
end
| false -> begin
(stackBlockAtLoc id tl)
end)
end))

let blockAtLoc = (fun ( m ) ( rl ) -> (match (rl) with
| InHeap -> begin
Some ((hp m))
end
| InStack (id) -> begin
(stackBlockAtLoc id (st m))
end))

let writeInBlock = (fun ( r ) ( v ) ( mb ) -> (Support.Heap.upd mb r v))

let rec changeStackBlockWithId = (fun ( f ) ( s ) ( ms ) -> (match (ms) with
| [] -> begin
[]
end
| h::tl -> begin
(match (((Support.Prims.fst h) = s)) with
| true -> begin
(((Support.Prims.fst h), (f (Support.Prims.snd h))))::tl
end
| false -> begin
(h)::(changeStackBlockWithId f s tl)
end)
end))

let rec writeInMemStack = (fun ( r ) ( ms ) ( s ) ( v ) -> (changeStackBlockWithId (writeInBlock r v) s ms))

let rec changeStackBlockSameIDs = (fun ( f ) ( s ) ( ms ) -> ())

let changeStackBlockWellFormed = (fun ( f ) ( s ) ( ms ) -> ())

let writeMemStackSameIDs = (fun ( r ) ( ms ) ( s ) ( v ) -> ())

let writeMemStackWellFormed = (fun ( r ) ( ms ) ( s ) ( v ) -> ())

let rec refExistsInStack = (fun ( r ) ( id ) ( ms ) -> (match (ms) with
| [] -> begin
false
end
| h::tl -> begin
(match (((Support.Prims.fst h) = id)) with
| true -> begin
(Support.Heap.contains (Support.Prims.snd h) r)
end
| false -> begin
(refExistsInStack r id tl)
end)
end))

let rec refExistsInStackId = (fun ( r ) ( id ) ( ms ) -> ())

let memIdUniq = (fun ( h ) ( tl ) -> ())

let refExistsInStackTail = (fun ( r ) ( id ) ( ms ) -> ())

let refExistsInMem = (fun ( r ) ( m ) -> (match ((refLoc r)) with
| InHeap -> begin
(Support.Heap.contains (hp m) r)
end
| InStack (id) -> begin
(refExistsInStack r id (st m))
end))

let rec writeMemStackExists = (fun ( rw ) ( r ) ( ms ) ( id ) ( idw ) ( v ) -> ())

let writeMemAux = (fun ( r ) ( m ) ( v ) -> (match ((refLoc r)) with
| InHeap -> begin
((Support.Heap.upd (hp m) r v), (Support.Prims.snd m))
end
| InStack (id) -> begin
((hp m), (writeInMemStack r (st m) id v))
end))

let writeMemAuxPreservesExists = (fun ( rw ) ( r ) ( m ) ( v ) -> ())

let writeMemAuxPreservesSids = (fun ( rw ) ( m ) ( v ) -> ())

let rec loopkupRefStack = (fun ( r ) ( id ) ( ms ) -> (match (ms) with
| h::tl -> begin
(match (((Support.Prims.fst h) = id)) with
| true -> begin
(Support.Heap.sel (Support.Prims.snd h) r)
end
| false -> begin
(loopkupRefStack r id tl)
end)
end))

let loopkupRef = (fun ( r ) ( m ) -> (match ((refLoc r)) with
| InHeap -> begin
(Support.Heap.sel (hp m) r)
end
| InStack (id) -> begin
(loopkupRefStack r id (st m))
end))

type ('b, 'tc, 'fc) ifthenelseT =
(('b, 'tc) Support.Prims.l_imp, ('b Support.Prims.l_not, 'fc) Support.Prims.l_imp) Support.Prims.l_and

let rec readAfterWriteStack = (fun ( rw ) ( r ) ( v ) ( id ) ( idw ) ( m ) -> ())

let readAfterWriteStackSameType = (fun ( rw ) ( r ) ( v ) ( id ) ( idw ) ( m ) -> ())

let readAfterWrite = (fun ( rw ) ( r ) ( v ) ( m ) -> ())

let readAfterWriteTrue = (fun ( rw ) ( r ) ( v ) ( m ) -> ())

let readAfterWriteFalse = (fun ( rw ) ( r ) ( v ) ( m ) -> ())

let readAfterWriteSameType = (fun ( rw ) ( r ) ( v ) ( m ) -> ())

let refExistsInMemTail = (fun ( r ) ( m ) -> ())

let loopkupRefStackTail = (fun ( r ) ( id ) ( ms ) -> ())

let readTailRef = (fun ( r ) ( m ) -> ())

let writeStackTail = (fun ( r ) ( id ) ( v ) ( ms ) -> ())

let writeTailRef = (fun ( r ) ( m ) ( v ) -> ())

let refExistsInMemSTailSids = (fun ( r ) ( id ) ( m0 ) ( m1 ) -> ())

let refExistsInMemTailSids = (fun ( r ) ( m0 ) ( m1 ) -> ())

type ('m0, 'm1, 'rs) canModify =
(Obj.t ref, (unit Support.Prims.b2t, (unit Support.Prims.b2t Support.Prims.l_not, (unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and) Support.Prims.l_imp) Support.Prims.l_imp) Support.Prims.l__Forall Support.Prims.l__ForallTyp

type ('a, 'r, 'v, 'm) mreads =
(unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and

let canModifyNone = (fun ( m ) -> ())

let canModifyWrite = (fun ( r ) ( v ) ( m ) -> ())

type ('a, 'r, 'h0, 'h1, 'init) allocateInBlock =
((unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and, (memblock, Support.Prims.heap, unit, unit) Support.Prims.l__Eq2) Support.Prims.l_and

let halloc = (fun ( init ) -> (failwith ("Not yet implemented")))

let salloc = (fun ( init ) -> (failwith ("Not yet implemented")))

let memread = (fun ( r ) -> (failwith ("Not yet implemented")))

let memwrite = (fun ( r ) ( v ) -> (failwith ("Not yet implemented")))

let pushStackFrame = (fun ( _ ) -> (failwith ("Not yet implemented")))

let popStackFrame = (fun ( _ ) -> (failwith ("Not yet implemented")))

type 'm mStackNonEmpty =
unit Support.Prims.b2t

let allRefs = (Support.Set.complement (Support.Set.empty ()))

let withNewScope = (fun ( mods ) ( body ) -> (let _7_457 = (pushStackFrame ())
in (let v = (body ())
in (let _7_460 = (popStackFrame ())
in v))))

let rec scopedWhile = (fun ( wg ) ( mods ) ( bd ) -> (match ((wg ())) with
| true -> begin
(let _7_499 = (withNewScope mods (Obj.magic bd))
in (scopedWhile wg mods bd))
end
| false -> begin
()
end))

let scopedWhile1 = (fun ( r ) ( lc ) ( 'loopInv ) ( mods ) ( bd ) -> (scopedWhile (Obj.magic (fun ( u ) -> (let _7_18302 = (memread r)
in (lc _7_18302)))) mods bd))

let scopedWhile2 = (fun ( ra ) ( rb ) ( lc ) ( 'loopInv ) ( mods ) ( bd ) -> (scopedWhile (Obj.magic (fun ( u ) -> (let _7_18340 = (memread ra)
in (let _7_18339 = (memread rb)
in (lc _7_18340 _7_18339))))) mods bd))




