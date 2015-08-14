
type ' a sstarray = 'a array

let asRef = (fun ( va ) -> ())

let readIndex = (fun ( r ) ( index ) 
		-> Array.get r index)

let writeIndex = (fun ( r ) ( index ) ( newV ) 
		-> Array.set r index newV)

let screateSeq = (fun ( init ) 
		-> failwith "NYI:screateSeq")

let hcreateSeq = (fun ( init ) 
		-> failwith "NYI:hcreateSeq")

let screate = (fun ( len ) ( init ) 
	-> Camlstack.mkarray len init) (*danger: remove no_scan if init has a type whose members can store pointers to OCaml Heap*)

let hcreate = (fun ( len ) ( init ) 
	-> Array.make len init)

let to_seq = (fun ( r ) 
		-> failwith "deprecated : to_seq. implement it using readIndex and a loop")

let length = (fun ( r ) -> Array.length r)


