module Box.Indexing

open FStar.Set
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap

type dh_id = int
abstract type ae_id = (i:(dh_id*dh_id){fst i <= snd i})

type id =
  | DH_id of dh_id
  | AE_id of ae_id

val generate_ae_id: i1:id{DH_id? i1} -> i2:id{DH_id? i2} -> Tot (i3:id{AE_id? i3})
let generate_ae_id i1 i2 =
  match i1,i2 with
  | DH_id i1',DH_id i2' ->
  if i1' <= i2' then
    AE_id (i1',i2')
  else
    AE_id (i2',i1')


val symmetric_id_generation: i1:id{AE_id? i1} -> i2:id{AE_id? i2} -> Lemma
  (requires (True))
  (ensures (forall id1 id2. generate_ae_id id1 id2 = generate_ae_id id2 id1))
  [SMTPat (generate_ae_id i1 i2)]
let symmetric_id_generation i1 i2 = ()

assume Index_hasEq: hasEq id
assume AE_Index_hasEq: hasEq ae_id

type id_freshness_table_key = id
type id_freshness_table_value = unit
type id_freshness_table_range = fun id_freshness_table_key -> id_freshness_table_value
let id_freshness_table_inv (f:MM.map' id_freshness_table_key id_freshness_table_range) = True

assume val id_freshness_table_region: (r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root})

assume val id_freshness_table: MM.t id_freshness_table_region id_freshness_table_key id_freshness_table_range id_freshness_table_inv


type id_honesty_table_key = dh_id
type id_honesty_table_value = b:bool{~prf_odh ==> b=false}
type id_honesty_table_range = fun id_honesty_table_key -> id_honesty_table_value
let id_honesty_table_inv (m:MM.map' id_honesty_table_key id_honesty_table_range) = 
  True//forall i. Some? (MM.sel m i) ==> MR.witnessed (MM.defined id_freshness_table (DH_id i))
       
assume val id_honesty_table_region: (r:MR.rid{ extends r root /\ is_eternal_region r /\ is_below r root /\ disjoint r id_freshness_table_region})
//let id_table_region = new_region root in

assume val id_honesty_table: MM.t id_honesty_table_region id_honesty_table_key id_honesty_table_range id_honesty_table_inv
//let id_table = MM.alloc #id_table_region #id #range #inv in

let fresh (i:id) h =
  MM.fresh id_freshness_table i h

type unfresh (i:id) =
  MR.witnessed (MM.defined id_freshness_table i)

val fresh_unfresh_contradiction: i:id -> ST unit
  (requires (fun h0 -> 
    unfresh i
  ))
  (ensures (fun h0 _ h1 ->
    ~(fresh i h1)
    /\ h0 == h1
  ))
let fresh_unfresh_contradiction i =
  MR.m_recall id_freshness_table;
  MR.testify (MM.defined id_freshness_table i);
  match MM.lookup id_freshness_table i with
  | Some () -> ()


val freshST: (i:id) -> ST unit
  (requires (fun h0 -> ~(unfresh i)))
  (ensures (fun h0 b h1 ->
    fresh i h1
  ))
let freshST i =
  MR.m_recall id_freshness_table;
  match MM.lookup id_freshness_table i with
  | None -> ()
  


val make_unfresh: (i:id) -> ST (unit)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    modifies (Set.singleton id_freshness_table_region) h0 h1
    /\ (forall (i:id). ~(fresh i h0) ==> ~(fresh i h1))
    /\ unfresh i
  ))
let make_unfresh i =
  MR.m_recall id_freshness_table;
  match MM.lookup id_freshness_table i with
  | Some i' -> ()
  | None ->
    MM.extend id_freshness_table i ()

private let measure_id (i:id) =
  match i with
  | DH_id i' -> 0
  | _ -> 1

val fixed: (i:id) -> Tot Type0 (decreases (measure_id i))
let rec fixed (i:id) =
  match i with
  | DH_id i' -> MR.witnessed (MM.defined id_honesty_table i')
  | AE_id (i1,i2) -> fixed (DH_id i1) /\ fixed (DH_id i2)
  
val honest: (i:id) -> Tot (t:Type0{t ==> fixed i}) (decreases (measure_id i))
let rec honest (i:id) =
  if prf_odh then
    match i with
    | DH_id i' -> MR.witnessed (MM.contains id_honesty_table i' true) /\ MR.witnessed (MM.defined id_honesty_table i')
    | AE_id (i1,i2) -> honest (DH_id i1) /\ honest (DH_id i2)
  else
    False

val dishonest: (i:id) -> Tot (t:Type0{(t /\ DH_id? i) ==> fixed i}) (decreases (measure_id i))
let rec dishonest (i:id) =
  match i with
  | DH_id i' -> MR.witnessed (MM.contains id_honesty_table i' false) /\ MR.witnessed (MM.defined id_honesty_table i')
  | AE_id (i1,i2) -> dishonest (DH_id i1) \/ dishonest (DH_id i2)


// Implement these two for the adversary
//val make_dishonest: (i:id) -> ST (unit) (decreases (measure_id i))
//  (requires (fun h0 -> 
//    unfresh i
//  ))
//  (ensures (fun h0 _ h1 -> dishonest i))
//let rec make_dishonest i =
//  MR.m_recall id_honesty_table;
//  match i with
//  | DH_id i' -> (
//    match MM.lookup id_honesty_table i' with
//    | Some v -> ()
//    | None -> MM.extend id_honesty_table i' false)
//  | AE_id (i1,i2) -> 
//    make_dishonest (DH_id i1);
//    make_dishonest (DH_id i2)
    

//val make_honest: (i:id) -> ST (unit)
//  (requires (fun h0 ->
//    unfresh i
//    /\ MM.fresh id_honesty_table i h0
//  ))
//  (ensures (fun h0 _ h1 -> honest i))
//let make_honest i =
//  MR.m_recall id_honesty_table;
//  MM.extend id_honesty_table i true;
//  ()

val honestST: i:id{fixed i} -> ST(b:bool{(b ==> honest i) /\ (not b ==> dishonest i)}) (decreases (measure_id i))
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1 
    /\ h0==h1
    /\ (honest i \/ dishonest i)
  ))
let rec honestST i =
  MR.m_recall id_honesty_table;
  match i with
  | DH_id i' -> (
    MR.testify (MM.defined id_honesty_table i');
    match MM.lookup id_honesty_table i' with
    |Some v -> 
      v)
  | AE_id (i1,i2) -> 
    let b1 = honestST (DH_id i1) in
    let b2 = honestST (DH_id i2) in
    b1 && b2
  

val honest_dishonest_lemma: dh_i:dh_id -> ST(unit)
  (requires (fun h -> fixed (DH_id dh_i)))
  (ensures (fun h0 _ h1 ->
    let i = DH_id dh_i in
    modifies_none h0 h1 /\
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

val honest_dishonest_contradiction_lemma: i:dh_id -> ST(unit)
  (requires (fun h -> honest (DH_id i) /\ dishonest (DH_id i)))
  (ensures (fun h0 _ h1 -> False
  ))
let honest_dishonest_contradiction_lemma i = 
  MR.testify(MM.contains id_honesty_table i true);
  MR.testify(MM.contains id_honesty_table i false)


////////////////////////////////////////////////////////////////////////////////////////////////
//  Data type and functions of ae_id, which is composed of two regular ids.
///////////////////////////////////////////////////////////////////////////////////////////////

//let ae_fresh i h =
//  ~(MM.defined id_freshness_table i h)


//type ae_unfresh (i:ae_id) =
//  MR.witnessed (MM.defined id_freshness_table i)

//val ae_make_unfresh: (i:ae_id) -> ST (unit)
//  (requires (fun h0 -> True))
//  (ensures (fun h0 _ h1 ->
//    modifies (Set.singleton id_freshness_table_region) h0 h1
//    /\ ae_unfresh i
//  ))
//let ae_make_unfresh i =
//  MR.m_recall id_freshness_table;
//  match MM.lookup id_freshness_table i with
//  | Some v -> ()
//  | None -> 
//    MM.extend id_freshness_table i ()
  
//type ae_honest k_i =
//  honest (fst k_i) /\ honest (snd k_i)
//
//type ae_dishonest (k_i:ae_id) =
//  dishonest (fst k_i) \/ dishonest (snd k_i)
//
//type ae_fixed (k_i:ae_id) = 
//  fixed (fst k_i) /\ fixed(snd k_i)
//  
//val ae_make_honest: i:ae_id -> ST unit
//  (requires (fun h0 -> honest i))
//  (ensures (fun h0 _ h1 ->
//    ae_honest i
//  ))
//
//val ae_honestST: k_i:ae_id{ae_fixed k_i} -> ST(b:bool{(b ==> (ae_honest k_i)) /\ (not b ==> (ae_dishonest k_i))})
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 ->
//    modifies_none h0 h1
//    /\ MR.m_contains id_honesty_table h1
//    /\ (ae_honest k_i \/ ae_dishonest k_i)
//    /\ ae_fixed k_i
//  ))
//let ae_honestST k_i =
//  let h1 = honestST (fst k_i) in 
//  let h2 = honestST (snd k_i) in
//  (h1 && h2)



//val ae_id_property_lemma: (i1:id) -> (i2:id) -> Lemma
//  (requires True)
//  (ensures (
//    let i3 = generate_ae_id i1 i2 in
//    (fixed i1 /\ fixed i2 ==> ae_fixed i3)
//    /\ (honest i1 /\ honest i2 ==> ae_honest i3)
//    /\ (dishonest i1 \/ dishonest i2 ==> ae_dishonest i3)
//  ))
//  [SMTPat (generate_ae_id i1 i2)]
//let ae_id_property_lemma i1 i2 = ()
//
