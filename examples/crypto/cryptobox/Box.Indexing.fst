module Box.Indexing

open FStar.Set
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap


// Make these abstract!
type id = UInt32.t
assume Index_hasEq: hasEq id
private type range = fun id -> bool
private let inv (f:MM.map' id range) = True
private let table = MM.alloc #root #id #range #inv 


//abstract type val honest: i:id -> Tot bool
let honest (i:id) =
  MR.witnessed (MM.contains table i true)

let dishonest (i:id) =
  MR.witnessed (MM.contains table i false)



val honestST: i:id -> St(b:bool{(b ==> honest i) /\ (not b ==> dishonest i)})
let honestST (i:id) =
  MR.m_recall table;
  match MM.lookup table i with
  |Some v -> 
//    MR.testify (MM.contains table i v);
    v
  |None -> 
    MM.extend table i true;
 //   MR.testify (MM.contains table i true);
    true


val lemma_hon_implies_not_dis: i:id -> w:(honest i)-> Lemma
  (requires (True))
  (ensures (honest i ==> ~(dishonest i)))
  [SMTPat (honest i)]
let lemma_hon_implies_not_dis i =
  ()


val lemma_dis_implies_not: i:id -> Lemma 
  (requires (True))
  (ensures (dishonest i ==> ~(honest i)))
  [SMTPat (dishonest i) ]
let lemma_dis_implies_not i = ()



type ae_id = (id*id)

let ae_honest (i1,i2:ae_id) =
  MR.witnessed (MM.contains table i1 true) /\
  MR.witnessed (MM.contains table i2 true)
  //honest i1 /\ honest i2

let ae_dishonest (i1,i2:ae_id) =
  MR.witnessed (MM.contains table i1 false) \/
  MR.witnessed (MM.contains table i2 false)
  //dishonest i1 \/ dishonest i2

val ae_honestST: i:(id*id) -> St(b:bool{(b ==> (ae_honest i)) /\ (not b ==> (ae_dishonest i))})
let ae_honestST (i1,i2) =
  let h1 = honestST i1 in 
  let h2 = honestST i2 in
  h1 && h2

val lemma_ae_dis_implies_not: i:ae_id -> Lemma 
  (requires (True))
  (ensures (ae_dishonest i ==> ~(ae_honest i)))
  [SMTPat (ae_honest i) ]
let lemma_ae_dis_implies_not i = ()

val lemma_ae_hon_implies_not_dis: i:ae_id -> Lemma 
  (requires (True))
  (ensures (ae_honest i ==> ~(ae_dishonest i)))
  [SMTPat (ae_honest i) ]
let lemma_ae_hon_implies_not_dis i = ()

//private type ae_range = fun (i:ae_id) -> (b:bool{b ==> honest (fst i) /\ honest (snd i)})
//private let ae_inv (f:MM.map' ae_id ae_range) = True
//private let ae_table = MM.alloc #root #ae_id #ae_range #ae_inv 
//
//
//
//assume val generate_ae_id: i1:id -> i2:id -> Tot (i3:ae_id{i3=(i1,i2)})
//
//
////assume val ae_honest: i:ae_id -> Tot (b:bool{b ==> (honest (fst i) /\ honest (snd i))})
//let ae_honest (i:ae_id) =
//  honest (fst i) /\ honest (snd i) /\
//  MR.witnessed (MM.contains ae_table i true)
//
//let ae_dishonest (i:ae_id) =
//  dishonest (fst i) \/ dishonest (snd i) \/
//  MR.witnessed (MM.contains ae_table i false)
//
//assume val lemma_ae_dis_implies_not: i:ae_id -> Lemma 
//  (requires (True))
//  (ensures (ae_dishonest i ==> ~(ae_honest i)))
//  [SMTPat (ae_dishonest i) ]
//  
//val ae_honestST: i:ae_id -> ST(b:bool{(b ==> ae_honest i) /\ (not b ==> ae_dishonest i)})
//  (requires (fun h0 -> True))
//  (ensures (fun h0 t h1 -> 
//    modifies (Set.singleton root) h0 h1 // precise enough?
//    ))
//let ae_honestST (i:ae_id) =
//  MR.m_recall ae_table;
//  match MM.lookup ae_table i with
//  |Some v -> 
//    v=true
//  |None -> 
//    MM.extend ae_table i false;
//    false
//
//
////val ae_honest: i:ae_id -> Tot (b:bool ==> (forall x. mem x i ==> honest x))
//
