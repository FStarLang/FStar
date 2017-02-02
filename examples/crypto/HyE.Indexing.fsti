module HyE.Indexing

type pke_id = UInt32.t
type ae_id = pke_id*UInt32.t


// Do lookups in the global table here
val pke_honest: pke_id -> Tot bool
val ae_honest: i:ae_id -> Tot (b:bool{b ==> pke_honest (fst i)})

val fresh_pke_id: unit -> Tot (i:pke_id{pke_honest i})

val fresh_ae_id: pke_id -> Tot UInt32.t
val dishonest_ae_id: pk_i:pke_id -> Tot (num:UInt32.t{not (ae_honest (pk_i,num))})

assume Index_hasEq: hasEq pke_id
