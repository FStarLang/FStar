module Box.Indexing

open FStar.Set
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap

type id = int
assume Index_hasEq: hasEq id
type range = fun id -> bool
let inv (f:MM.map' id range) = True

assume val id_table_region: (r:MR.rid{ extends r root /\ is_eternal_region r /\ is_below r root})
//let id_table_region = new_region root in


assume val id_table: MM.t id_table_region id range inv
//let id_table = MM.alloc #id_table_region #id #range #inv in

//let id_init =
//  let id_table_region = new_region root in
//  let id_table = MM.alloc #id_table_region #id #range #inv in
//  ()


type honest (i:id) =
  MR.witnessed (MM.contains id_table i true)

type dishonest (i:id) =
  MR.witnessed (MM.contains id_table i false)

type fixed (i:id) =
  MR.witnessed (MM.defined id_table i)

val make_dishonest: (i:id) -> ST (unit)
  (requires (fun h0 -> MM.fresh id_table i h0))
  (ensures (fun h0 _ h1 -> dishonest i))
let make_dishonest i =
  MM.extend id_table i false;
  ()

val make_honest: (i:id) -> ST (unit)
  (requires (fun h0 -> MM.fresh id_table i h0))
  (ensures (fun h0 _ h1 -> honest i))
let make_honest i =
  MM.extend id_table i true;
  ()
  

val honestST: i:id{fixed i} -> ST(b:bool{(b ==> honest i) /\ (not b ==> dishonest i)})
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1 
    /\ MR.m_contains id_table h1
  ))
let honestST i =
  MR.m_recall id_table;
  MR.testify(MM.defined id_table i);
  match MM.lookup id_table i with
  |Some v -> 
    v

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

val honest_dishonest_lemma: i:id -> ST(unit)
  (requires (fun h -> fixed i))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1 /\
    ( dishonest i \/ honest i ) /\
    ( ~(honest i) ==> dishonest i ) /\
    ( ~(dishonest i) ==> honest i ) /\
//    ( honest i ==> ~(dishonest i) ) /\ //This cannot be proven.
    True
  ))
let honest_dishonest_lemma i = 
  let h = get() in
  MR.testify (MM.defined id_table i); 
  match MM.lookup id_table i with
  |Some v -> ()

val honest_dishonest_contradiction_lemma: i:id -> ST(unit)
  (requires (fun h -> honest i /\ dishonest i))
  (ensures (fun h0 _ h1 -> False
  ))
let honest_dishonest_contradiction_lemma i = 
  MR.testify(MM.contains id_table i true);
  MR.testify(MM.contains id_table i false);
  ()


type ae_honest k_i =
  honest (fst k_i.i) /\ honest (snd k_i.i)

type ae_dishonest (k_i:ae_id) =
  dishonest (fst k_i.i) \/ dishonest (snd k_i.i)

type ae_fixed (k_i:ae_id) = 
  fixed (fst k_i.i) /\ fixed(snd k_i.i)
  


val ae_honestST: k_i:ae_id{ae_fixed k_i} -> ST(b:bool{(b ==> (ae_honest k_i)) /\ (not b ==> (ae_dishonest k_i))})
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1
    /\ MR.m_contains id_table h1
    /\ (ae_honest k_i \/ ae_dishonest k_i)
    /\ ae_fixed k_i
  ))
let ae_honestST k_i =
  let h1 = honestST (fst k_i.i) in 
  let h2 = honestST (snd k_i.i) in
  (h1 && h2)



