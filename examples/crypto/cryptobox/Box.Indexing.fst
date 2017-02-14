module Box.Indexing

open FStar.Set
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap

type id = int
assume Index_hasEq: hasEq id

type id_freshness_table_key = id
type id_freshness_table_value = unit
type id_freshness_table_range = fun id_freshness_table_key -> id_freshness_table_value
let id_freshness_table_inv (f:MM.map' id_freshness_table_key id_freshness_table_range) = True

assume val id_freshness_table_region: (r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root})

assume val id_freshness_table: MM.t id_freshness_table_region id_freshness_table_key id_freshness_table_range id_freshness_table_inv

type id_honesty_table_key = id
type id_honesty_table_value = bool
type id_honesty_table_range = fun id_honesty_table_key -> id_honesty_table_value
let id_honesty_table_inv (m:MM.map' id_honesty_table_key id_honesty_table_range) = 
  forall i. Some? (MM.sel m i) ==> MR.witnessed (MM.defined id_freshness_table i)
       
assume val id_honesty_table_region: (r:MR.rid{ extends r root /\ is_eternal_region r /\ is_below r root})
//let id_table_region = new_region root in

assume val id_honesty_table: MM.t id_honesty_table_region id_honesty_table_key id_honesty_table_range id_honesty_table_inv
//let id_table = MM.alloc #id_table_region #id #range #inv in

val fresh: (i:id) -> h:mem -> Tot Type0
let fresh (i:id) h =
  MM.contains id_freshness_table i () h

type unfresh (i:id) =
  MR.witnessed (MM.contains id_freshness_table i ())

val make_unfresh: (i:id) -> ST (unit)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    modifies (Set.singleton id_freshness_table_region) h0 h1
    /\ unfresh i
  ))
let make_unfresh i =
  MR.m_recall id_freshness_table;
  match MM.lookup id_freshness_table i with
  | Some i' -> ()
  | None ->
    MM.extend id_freshness_table i ();
    ()

type honest (i:id) =
  MR.witnessed (MM.contains id_honesty_table i true)

type dishonest (i:id) =
  MR.witnessed (MM.contains id_honesty_table i false)

type fixed (i:id) =
  MR.witnessed (MM.defined id_honesty_table i)


val make_dishonest: (i:id) -> ST (unit)
  (requires (fun h0 -> 
    MR.witnessed (MM.defined id_freshness_table i)
    /\ MM.fresh id_honesty_table i h0
  ))
  (ensures (fun h0 _ h1 -> dishonest i))
let make_dishonest i =
  MM.extend id_honesty_table i false;
  ()

val make_honest: (i:id) -> ST (unit)
  (requires (fun h0 ->
    MR.witnessed (MM.defined id_freshness_table i)
    /\ MM.fresh id_honesty_table i h0
  ))
  (ensures (fun h0 _ h1 -> honest i))
let make_honest i =
  MM.extend id_honesty_table i true;
  ()
  

val honestST: i:id{fixed i} -> ST(b:bool{(b ==> honest i) /\ (not b ==> dishonest i)})
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1 
    /\ MR.m_contains id_honesty_table h1
  ))
let honestST i =
  MR.m_recall id_honesty_table;
  MR.testify(MM.defined id_honesty_table i);
  match MM.lookup id_honesty_table i with
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
  MR.testify (MM.defined id_honesty_table i); 
  match MM.lookup id_honesty_table i with
  |Some v -> ()

val honest_dishonest_contradiction_lemma: i:id -> ST(unit)
  (requires (fun h -> honest i /\ dishonest i))
  (ensures (fun h0 _ h1 -> False
  ))
let honest_dishonest_contradiction_lemma i = 
  MR.testify(MM.contains id_honesty_table i true);
  MR.testify(MM.contains id_honesty_table i false);
  ()

type ae_fresh i h =
  fresh (fst i.i) h /\ fresh (snd i.i) h
  

type ae_unfresh (i:ae_id) =
  unfresh (fst i.i) /\ unfresh (snd i.i)

val ae_make_unfresh: (i:ae_id) -> ST (unit)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    modifies (Set.singleton id_freshness_table_region) h0 h1
    /\ ae_unfresh i
  ))
let ae_make_unfresh i =
  make_unfresh (fst i.i);
  make_unfresh (snd i.i);
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
    /\ MR.m_contains id_honesty_table h1
    /\ (ae_honest k_i \/ ae_dishonest k_i)
    /\ ae_fixed k_i
  ))
let ae_honestST k_i =
  let h1 = honestST (fst k_i.i) in 
  let h2 = honestST (snd k_i.i) in
  (h1 && h2)



