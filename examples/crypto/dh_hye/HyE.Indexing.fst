module HyE.Indexing

open FStar.Set
open FStar.HyperHeap

// Make these abstract!
type id = UInt32.t
type ae_id = (id*id)

//type log_t: (r:rid) = 
//  Log: m_rref r (seq id) grows
//
//val log: log_t

assume val generate_ae_id: i1:id -> i2:id -> Tot (i3:ae_id{i3=(i1,i2)})

assume val honest: i:id -> Tot bool
//let honest i =
//  let root = HyperHeap.get() in
//  if m_contains log root then
//    let id_log = m_read log in
//    match seq_find (fun entry -> entry = i) id_log with
//    | Some i' -> true
//    | None -> false
//  else
//    log =

assume val ae_honest: i:ae_id -> Tot (b:bool{b ==> (honest (fst i) /\ honest (snd i))})
//val ae_honest: i:ae_id -> Tot (b:bool ==> (forall x. mem x i ==> honest x))

assume Index_hasEq: hasEq id
