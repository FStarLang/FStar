module Box.Indexing

open FStar.Set
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap


// Make these abstract!
type id = UInt32.t
private type range = fun id -> bool
private let inv (f:MM.map' id range) = True
private let table = MM.alloc #root #id #range #inv 


//abstract type val honest: i:id -> Tot bool
let honest (i:id) =
  MR.witnessed (MM.contains table i true)

let dishonest (i:id) =
  MR.witnessed (MM.contains table i false)

assume val lemma_dis_implies_not: i:id -> Lemma 
  (requires (True))
  (ensures (dishonest i ==> ~(honest i)))
  [SMTPat (dishonest i) ]


val honestST: i:id -> St(b:bool{(b ==> honest i) /\ (not b ==> dishonest i)})
let honestST (i:id) =
  MR.m_recall table;
  match MM.lookup table i with
  |Some v -> 
    v=true
  |None -> 
    MM.extend table i false;
    false

type ae_id = (id*id)
private type ae_range = fun (i:ae_id) -> (b:bool{b ==> honest (fst i) /\ honest (snd i)})
private let ae_inv (f:MM.map' ae_id ae_range) = True
private let ae_table = MM.alloc #root #ae_id #ae_range #ae_inv 



assume val generate_ae_id: i1:id -> i2:id -> Tot (i3:ae_id{i3=(i1,i2)})


//assume val ae_honest: i:ae_id -> Tot (b:bool{b ==> (honest (fst i) /\ honest (snd i))})
let ae_honest (i:ae_id) =
  honest (fst i) /\ honest (snd i) /\
  MR.witnessed (MM.contains ae_table i true)

let ae_dishonest (i:ae_id) =
  dishonest (fst i) \/ dishonest (snd i) \/
  MR.witnessed (MM.contains ae_table i false)

assume val lemma_ae_dis_implies_not: i:ae_id -> Lemma 
  (requires (True))
  (ensures (ae_dishonest i ==> ~(ae_honest i)))
  [SMTPat (ae_dishonest i) ]
  
val ae_honestST: i:ae_id -> ST(b:bool{(b ==> ae_honest i) /\ (not b ==> ae_dishonest i)})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> 
    modifies (Set.singleton root) h0 h1 // precise enough?
    ))
let ae_honestST (i:ae_id) =
  MR.m_recall ae_table;
  match MM.lookup ae_table i with
  |Some v -> 
    v=true
  |None -> 
    MM.extend ae_table i false;
    false


//val ae_honest: i:ae_id -> Tot (b:bool ==> (forall x. mem x i ==> honest x))

assume Index_hasEq: hasEq id
