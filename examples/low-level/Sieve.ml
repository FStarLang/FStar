

let marked = (fun ( n ) ( f ) ( m ) -> (f m))

let mark = (fun ( n ) ( f ) ( index ) ( indx ) -> (match ((indx = index)) with
| true -> begin
true
end
| false -> begin
(f indx)
end))



let innerLoop = (fun ( n ) ( lo ) ( li ) ( res ) ( initres ) -> 
	(let _13_178 = (SSTCombinators.scopedWhile 
	((fun ( u ) -> (((SST.memread li) * (SST.memread lo)) < n))) () ((fun ( u ) -> (let liv = (SST.memread li)
in (let lov = (SST.memread lo)
in (let resv = (SST.memread res)
in (let _13_175 = (SST.memwrite li (liv + 1))
in (SST.memwrite res (mark n resv (lov * liv))
); print_int (lov * liv); print_string ";";
))))))) in ()
))



let outerLoopBody = ((fun ( n ) ( lo ) ( res ) ( u ) -> (let initres = (SST.memread res)
in (let lov = (SST.memread lo)
in (let li = (SST.salloc 0)
in (let liv = (SST.memread li)
in (let _13_244 = (innerLoop n lo li res initres)
in (let newres = (SST.memread res)
in (let _13_247 = (SST.memwrite lo (lov + 1))
in ())))))))))

let outerLoop = (fun ( n ) ( lo ) ( res ) -> (SSTCombinators.scopedWhile ((fun ( u ) -> ((SST.memread lo) < n))) () (outerLoopBody n lo res)))



let sieve = (fun ( n ) ( u ) -> (let lo = (SST.salloc 2)
in (let f = (fun ( x ) -> false)
in (let res = (SST.salloc f)
in (let _13_305 = (outerLoop n lo res)
in (SST.memread res))))))

let sieveFull = (fun ( n ) -> (let _13_318 = (SST.pushStackFrame ())
in (let res = (sieve n ())
in (let _13_321 = (SST.popStackFrame ())
in res))))

let rec firstN = (fun ( n ) -> (match (n) with
| 0 -> begin
[]
end
| _ -> begin
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
