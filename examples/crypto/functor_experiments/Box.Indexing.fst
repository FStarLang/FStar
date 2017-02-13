module Box.Indexing

open FStar.Set
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap


// This should be UInt32?
type id = int
assume Index_hasEq: hasEq id
type range = fun id -> bool
let inv (f:MM.map' id range) = True
let table = MM.alloc #root #id #range #inv 


//abstract type val honest: i:id -> Tot bool
let honest (i:id) =
  MR.witnessed (MM.contains table i true)

let dishonest (i:id) =
  MR.witnessed (MM.contains table i false)


val make_dishonest: (i:id) -> ST (unit)
  (requires (fun h0 -> MM.fresh table i h0))
  (ensures (fun h0 _ h1 -> dishonest i))
let make_dishonest i =
  MM.extend table i false;
  ()
  
val honestST: i:id -> St(b:bool{(b ==> honest i) /\ (not b ==> dishonest i)})
let honestST (i:id) =
  MR.m_recall table;
  match MM.lookup table i with
  |Some v -> 
    v
  |None -> 
    MM.extend table i true;
    true

//val lemma_hon_implies_not_dis: i:id -> Lemma
//  (requires (True))
//  (ensures (honest i ==> ~(dishonest i)))
//  [SMTPat (honest i)]
//let lemma_hon_implies_not_dis i =
//  ()

abstract type ae_id = 
  | AE_id: i:(id*id){fst i <= snd i} -> ae_id

val generate_ae_id: i1:id -> i2:id -> Tot (i3:ae_id{fst i3.i <= snd i3.i})
let generate_ae_id i1 i2 =
  if i1 <= i2 then
    AE_id (i1,i2)
  else
    AE_id (i2,i1)

val unique_id_generation: i1:id -> i2:id -> Lemma
  (requires (True))
  (ensures (forall id1 id2. generate_ae_id id1 id2 = generate_ae_id id2 id1))
  [SMTPat (generate_ae_id i1 i2)]
let unique_id_generation i1 i2 = ()

let ae_honest (k_i:ae_id) =
  honest (fst k_i.i) /\ honest (snd k_i.i)

let ae_dishonest (k_i:ae_id) =
  dishonest (fst k_i.i) \/ dishonest (snd k_i.i)

val ae_honestST: k_i:ae_id -> St(b:bool{(b ==> (ae_honest k_i)) /\ (not b ==> (ae_dishonest k_i))})
let ae_honestST k_i =
  let h1 = honestST (fst k_i.i) in 
  let h2 = honestST (snd k_i.i) in
  h1 && h2

