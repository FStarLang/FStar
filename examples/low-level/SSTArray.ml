
type ' a sstarray =
' a Seq.seq ref

let asRef = (fun ( va ) -> ())

let readIndex = (fun ( r ) ( index ) -> (let rv = (SST.memread r)
in (Seq.index rv index)))

let writeIndex = (fun ( r ) ( index ) ( newV ) -> (let rv = (SST.memread r)
in (SST.memwrite r (Seq.upd rv index newV))))

let screateSeq = (fun ( init ) -> (SST.salloc init))

let hcreateSeq = (fun ( init ) -> (SST.halloc init))

let screate = (fun ( len ) ( init ) -> (SST.salloc (Seq.create len init)))

let hcreate = (fun ( len ) ( init ) -> (SST.halloc (Seq.create len init)))

let to_seq = (fun ( r ) -> (SST.memread r))

let length = (fun ( r ) -> (let _22_6254 = (SST.memread r)
in (Seq.length _22_6254)))




