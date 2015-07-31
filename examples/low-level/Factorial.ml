
let rec factorial = (fun ( n ) -> (match (n) with
| 0 -> begin
1
end
| n -> begin
(n * (factorial (n - 1)))
end))

type (' n, ' li, ' m) factorialGuardLC =
unit Support.Prims.b2t

let factorialGuard = (Obj.magic (fun ( n ) ( li ) ( u ) -> (not (((SST.memread li) = n)))))

type (' li, ' res, ' m) loopInv =
(((unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t Support.Prims.l_not) Support.Prims.l_and

let factorialLoopBody = (Obj.magic (fun ( n ) ( li ) ( res ) ( u ) -> (let liv = (SST.memread li)
in (let resv = (SST.memread res)
in (let _12_25 = (SST.memwrite li (liv + 1))
in (SST.memwrite res ((liv + 1) * resv)))))))

let factorialLoop = (fun ( n ) ( li ) ( res ) -> (SSTCombinators.scopedWhile (Obj.magic (factorialGuard n li)) (Set.union (Set.singleton (Heap.Ref ((), (Obj.magic li)))) (Set.singleton (Heap.Ref ((), (Obj.magic res))))) (factorialLoopBody n li res)))

let loopyFactorial = (fun ( n ) -> (let li = (SST.salloc 0)
in (let res = (SST.salloc 1)
in (let _12_48 = (factorialLoop n li res)
in (let v = (SST.memread res)
in v)))))

let loopyFactorial2 = (fun ( n ) -> (SSTCombinators.withNewScope Set.empty (fun ( u ) -> (let li = (SST.salloc 0)
in (let res = (SST.salloc 1)
in (let _12_68 = (SSTCombinators.scopedWhile1 li (fun ( liv ) -> (not ((liv = n)))) () (Set.union (Set.singleton (Heap.Ref ((), (Obj.magic li)))) (Set.singleton (Heap.Ref ((), (Obj.magic res))))) (Obj.magic (Obj.magic (fun ( u ) -> (let liv = (SST.memread li)
in (let resv = (SST.memread res)
in (let _12_65 = (SST.memwrite li (liv + 1))
in (SST.memwrite res ((liv + 1) * resv)))))))))
in (let v = (SST.memread res)
in v)))))))




