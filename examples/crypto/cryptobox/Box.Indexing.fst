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

let id_table_color = -1
val id_table_region: (r:MR.rid{color r = id_table_color /\ extends r root /\ is_eternal_region r /\ is_below r root})
let id_table_region = new_colored_region root id_table_color


//val id_table: MM.t
let id_table = MM.alloc #id_table_region #id #range #inv 


//abstract type val honest: i:id -> Tot bool
type honest (i:id) =
  MR.witnessed (MM.contains id_table i true)

type dishonest (i:id) =
  MR.witnessed (MM.contains id_table i false)


val make_dishonest: (i:id) -> ST (unit)
  (requires (fun h0 -> MM.fresh id_table i h0))
  (ensures (fun h0 _ h1 -> dishonest i))
let make_dishonest i =
  MM.extend id_table i false;
  ()

val honestST: i:id -> ST(b:bool{(b ==> honest i) /\ (not b ==> dishonest i)})
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_one id_table_region h0 h1 
    /\ MR.m_contains id_table h1
  ))
let honestST (i:id) =
  MR.m_recall id_table;
  match MM.lookup id_table i with
  |Some v -> 
    v
  |None -> 
    MM.extend id_table i true;
    true

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


//val ae_honest: (k_i:ae_id) -> Tot Type0 //(t:Type{t ==> honest (fst k_i.i) /\ honest (snd k_i.i)})
type ae_honest k_i =
  honest (fst k_i.i) /\ honest (snd k_i.i)


type ae_dishonest (k_i:ae_id) =
  dishonest (fst k_i.i) \/ dishonest (snd k_i.i)

val ae_honestST: k_i:ae_id -> ST(b:bool{(b ==> (ae_honest k_i)) /\ (not b ==> (ae_dishonest k_i))})
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_one id_table_region h0 h1 
    /\ MR.m_contains id_table h1
    ///\ MR.m_sel h1 id_table == snoc (MR.m_sel h0 id_table) i
  ))
let ae_honestST k_i =
  let h1 = honestST (fst k_i.i) in 
  let h2 = honestST (snd k_i.i) in
  h1 && h2



