
type (' divisor, ' n) divides =
(int, unit Support.Prims.b2t) Support.Prims.l__Exists

let divisorSmall = (fun ( n ) ( divisor ) -> ())

let isNotPrimeIf2 = (fun ( n ) ( m ) -> ())

type ' n isNotPrime =
(int, ((unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and, (unit, unit) divides) Support.Prims.l_and) Support.Prims.l__Exists

type (' n, ' lo, ' li, ' m) innerGuardLC =
unit Support.Prims.b2t

type (' a, ' n) vector =
Support.Prims.nat  ->  ' a

let marked = (fun ( n ) ( f ) ( m ) -> (f m))

let mark = (fun ( n ) ( f ) ( index ) ( indx ) -> (match ((indx = index)) with
| true -> begin
true
end
| false -> begin
(f indx)
end))

type (' a, ' b, ' c, ' m, ' ra, ' rb, ' rc) distinctRefsExists3 =
(((((unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t) Support.Prims.l_and, (' a ref, ' b ref, unit, unit) Support.Prims.l__Eq2 Support.Prims.l_not) Support.Prims.l_and, (' b ref, ' c ref, unit, unit) Support.Prims.l__Eq2 Support.Prims.l_not) Support.Prims.l_and, (' a ref, ' c ref, unit, unit) Support.Prims.l__Eq2 Support.Prims.l_not) Support.Prims.l_and

let rec markMultiplesUpto = (fun ( n ) ( lo ) ( upto ) ( f ) -> (match (upto) with
| 0 -> begin
f
end
| _14_67 -> begin
(mark n (markMultiplesUpto n lo (upto - 1) f) ((upto - 1) * lo))
end))

type (' n, ' lo, ' upto, ' init, ' neww) markedIffMultipleOrInit =
(((int, unit Support.Prims.b2t) Support.Prims.l__Forall, (int, (unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_imp) Support.Prims.l__Forall) Support.Prims.l_and, (int, (unit Support.Prims.b2t, (unit Support.Prims.b2t, (unit, unit) divides) Support.Prims.l_or) Support.Prims.l_imp) Support.Prims.l__Forall) Support.Prims.l_and

type (' n, ' lo, ' li, ' res, ' initres, ' m) innerLoopInv =
(((Support.Prims.nat, Support.Prims.nat  ->  bool, Support.Prims.nat, unit, unit, unit, unit) distinctRefsExists3, unit Support.Prims.b2t) Support.Prims.l_and, (unit, unit, unit, unit, unit) markedIffMultipleOrInit) Support.Prims.l_and

type (' n, ' bitv, ' lo) multiplesMarked2 =
(int, (unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_imp) Support.Prims.l__Forall

type (' n, ' lo, ' init, ' neww) markedIffDividesOrInit2 =
(((int, unit Support.Prims.b2t) Support.Prims.l__Forall, (int, (unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_imp) Support.Prims.l__Forall) Support.Prims.l_and, (int, (unit Support.Prims.b2t, (unit Support.Prims.b2t, (unit, unit) divides) Support.Prims.l_or) Support.Prims.l_imp) Support.Prims.l__Forall) Support.Prims.l_and

type (' n, ' lo, ' init, ' neww) markedIffDividesOrInit =
(int, (unit Support.Prims.b2t, (unit Support.Prims.b2t, (unit, unit) divides) Support.Prims.l_or) Support.Prims.l_iff) Support.Prims.l__Forall

type (' n, ' bitv, ' lo) multiplesMarked =
(int, ((unit, unit) divides, unit Support.Prims.b2t) Support.Prims.l_imp) Support.Prims.l__Forall

let multiplesMarkedAsDivides = (fun ( n ) ( bitv ) ( lo ) -> ())

let multiplesMarkedAsDividesIff = (fun ( n ) ( bitv ) ( newv ) ( lo ) -> ())

let innerLoop = (fun ( n ) ( lo ) ( li ) ( res ) ( initres ) -> (let _14_178 = (SSTCombinators.scopedWhile (Obj.magic (fun ( u ) -> (((SST.memread li) * (SST.memread lo)) < n))) () (Obj.magic (fun ( u ) -> (let liv = (SST.memread li)
in (let lov = (SST.memread lo)
in (let resv = (SST.memread res)
in (let _14_175 = (SST.memwrite li (liv + 1))
in (SST.memwrite res (mark n resv (lov * liv))))))))))
in (let newv = (SST.memread res)
in (let lov = (SST.memread lo)
in ()))))

type (' a, ' b, ' m, ' ra, ' rb) distinctRefsExists2 =
((unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and, (' a ref, ' b ref, unit, unit) Support.Prims.l__Eq2 Support.Prims.l_not) Support.Prims.l_and

type (' n, ' lo, ' m) outerGuardLC =
unit Support.Prims.b2t

type (' n, ' lo, ' neww) markedIffHasDivisorSmallerThan =
(int, (unit Support.Prims.b2t, (int, (unit Support.Prims.b2t, (unit, unit) divides) Support.Prims.l_and) Support.Prims.l__Exists) Support.Prims.l_iff) Support.Prims.l__Forall

let markedIffHasDivisorSmallerThanInc = (fun ( n ) ( lo ) ( old ) ( neww ) -> ())

type (' n, ' neww) allUnmarked =
(int, unit Support.Prims.b2t) Support.Prims.l__Forall

let markedIffHasDivisorSmallerThan2 = (fun ( n ) ( neww ) -> ())

type (' n, ' lo, ' res, ' m) outerLoopInv =
((((Support.Prims.nat, Support.Prims.nat  ->  bool, unit, unit, unit) distinctRefsExists2, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t) Support.Prims.l_and, (unit, unit, unit) markedIffHasDivisorSmallerThan) Support.Prims.l_and

let outerLoopBody = (Obj.magic (fun ( n ) ( lo ) ( res ) ( u ) -> (let initres = (SST.memread res)
in (let lov = (SST.memread lo)
in (let li = (SST.salloc 0)
in (let liv = (SST.memread li)
in (let _14_244 = (innerLoop n lo li res initres)
in (let newres = (SST.memread res)
in (let _14_247 = (SST.memwrite lo (lov + 1))
in ())))))))))

let outerLoop = (fun ( n ) ( lo ) ( res ) -> (SSTCombinators.scopedWhile (Obj.magic (fun ( u ) -> ((SST.memread lo) < n))) () (outerLoopBody n lo res)))

type (' n, ' neww) markedIffNotPrime =
(int, (unit Support.Prims.b2t, unit isNotPrime) Support.Prims.l_iff) Support.Prims.l__Forall

let lessTrans = (fun ( n ) ( m ) ( d ) -> ())

let isNotPrimeIf = (fun ( n ) ( m ) -> ())

let sieve = (fun ( n ) ( u ) -> (let lo = (SST.salloc 2)
in (let f = (fun ( x ) -> false)
in (let res = (SST.salloc f)
in (let _14_305 = (outerLoop n lo res)
in (SST.memread res))))))

let sieveFull = (fun ( n ) -> (let _14_318 = (SST.pushStackFrame ())
in (let res = (sieve n ())
in (let _14_321 = (SST.popStackFrame ())
in res))))

let rec firstN = (fun ( n ) -> (match (n) with
| 0 -> begin
[]
end
| _14_327 -> begin
((n - 1))::(firstN (n - 1))
end))

let toBool = (fun ( n ) ( f ) -> (Support.List.mapT (fun ( x ) -> (match ((x < n)) with
| true -> begin
(f x)
end
| false -> begin
false
end)) (firstN n)))

let rec listOfTruesAux = (fun ( n ) ( max ) ( f ) -> (match ((max <= 2)) with
| true -> begin
[]
end
| false -> begin
(match ((not ((f (max - 1))))) with
| true -> begin
((max - 1))::(listOfTruesAux n (max - 1) f)
end
| false -> begin
(listOfTruesAux n (max - 1) f)
end)
end))

let listOfTrues = (fun ( n ) ( f ) -> (listOfTruesAux n n f))

let sieveAsList = (fun ( n ) -> (let sieveRes = (sieveFull n)
in (toBool n sieveRes)))

let sieveUnfolded = (fun ( n ) ( u ) -> (let lo = (SST.salloc 2)
in (let f = (fun ( x ) -> false)
in (let res = (SST.salloc f)
in (let _14_389 = (SSTCombinators.scopedWhile (Obj.magic (fun ( u ) -> ((SST.memread lo) < n))) () (Obj.magic (fun ( u ) -> (let initres = (SST.memread res)
in (let lov = (SST.memread lo)
in (let li = (SST.salloc 0)
in (let liv = (SST.memread li)
in (let _14_383 = (innerLoop n lo li res initres)
in (let newres = (SST.memread res)
in (let _14_386 = (SST.memwrite lo (lov + 1))
in ()))))))))))
in (SST.memread res))))))

type (' n, ' lo, ' li, ' res, ' initres, ' m) innerLoopInv2 =
((((unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t) Support.Prims.l_and, (unit, unit, unit, unit, unit) markedIffMultipleOrInit) Support.Prims.l_and

type (' n, ' lo, ' res, ' m) outerLoopInv2 =
((((unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t) Support.Prims.l_and, unit Support.Prims.b2t) Support.Prims.l_and, (unit, unit, unit) markedIffHasDivisorSmallerThan) Support.Prims.l_and




