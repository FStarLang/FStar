module HyE.Indexing

type pke_id = UInt32.t
type ae_id = pke_id*UInt32.t


// Do lookups in the global table here
val pke_honest: pke_id -> Tot bool
val ae_honest: i:ae_id -> Tot (b:bool{b ==> pke_honest (fst i)})

val fresh_pke_id: unit -> Tot (i:pke_id{pke_honest i})

// TODO: Try typechecking without refinements!
val fresh_ae_id: pk_id:pke_id -> Tot (k_id:ae_id{fst k_id = pk_id /\ (pke_honest pk_id ==> b2t (ae_honest k_id))})
val dishonest_ae_id: pk_id:pke_id -> Tot (k_id:ae_id{not (ae_honest k_id) && fst k_id = pk_id})

assume Index_hasEq: hasEq pke_id
