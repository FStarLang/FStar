module HyE.Indexing

open FStar.Seq

module MM = MonotoneMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef
module MS = FStar.Monotonic.Seq

type pke_id = MR.rid
type ae_id = pke_id*UInt32.t

type ae_id_table (r:pke_id) = MR.m_rref r (seq UInt32.t) MS.grows


type pke_id_to_ae_ids = fun (pk_id:pke_id) -> (ae_id_table pk_id)


let trivial_invariant (m:MM.map' pke_id pke_id_to_ae_ids)  = True


abstract let table_region: MR.rid = new_region HH.root
let pke_ae_id_table: MM.t table_region pke_id pke_id_to_ae_ids trivial_invariant = 
  MM.alloc #table_region #pke_id #pke_id_to_ae_ids #trivial_invariant


// Do lookups in the global table here
val pke_honest: pke_id -> MR.rid -> GTot Type0
let pke_honest pk_id h =
  MR.witnessed (MM.defined pke_ae_id_table pk_id)
  

val ae_honest: k_id:ae_id -> h:MR.rid -> GTot (b:Type0)//{b ==> pke_honest (fst k_id) h})
let ae_honest k_id h =
  MR.witnessed (MR.rid_exists (fst k_id)) /\
  pke_honest (fst k_id) h /\
  MR.witnessed (MM.contains (fst k_id) k_id)

val fresh_pke_id: unit -> Tot (i:pke_id{pke_honest i})
val is_fresh_pke_id: pke_id -> HS.mem-> GTot bool
let is_fresh_pke_id pk_id h =
  MM.sel (MR.m_sel h pke_ae_id_table) pk_id = None

// TODO: Try typechecking without refinements!
val fresh_ae_id: pk_id:pke_id -> Tot (k_id:ae_id{fst k_id = pk_id /\ (pke_honest pk_id ==> b2t (ae_honest k_id))})
val dishonest_ae_id: pk_id:pke_id -> Tot (k_id:ae_id{not (ae_honest k_id) && fst k_id = pk_id})

assume Index_hasEq: hasEq pke_id
