module Test

type rw =
  | Reader
  | Writer

new type id
new type rid
new type rref : rid -> Type0 -> Type0
new type entry : id -> Type0
new type seq : Type0 -> Type0

type state (i:id) (rw:rw) =
  | State: #region:rid 
         -> #peer_region:rid
         -> log: rref (if rw=Reader then peer_region else region) (seq (entry i)) // ghost, subject to cryptographic assumption
         -> state i rw

type writer i = s:state i Writer
type reader i = s:state i Reader

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we might drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: reader_parent:rid -> writer_parent:rid -> i:id -> ST (reader i * writer i)
  (requires (fun h0 -> HyperHeap.disjoint reader_parent writer_parent))
  (ensures  (fun h0 (rw:reader i * writer i) h1 ->
           let r = fst rw in 
           let w = snd rw in 
           (* let bang = fun x -> sel h1 x in  *)
           modifies Set.empty h0 h1
         /\ w.region = r.peer_region
         /\ r.region = w.peer_region
         /\ extends (w.region) writer_parent
         /\ extends (r.region) reader_parent
         /\ fresh_region w.region h0 h1
         /\ fresh_region r.region h0 h1
         /\ op_Equality #(rref w.region (seq (entry i))) w.log r.log  //the explicit annotation here 
         /\ contains_ref w.counter h1
         /\ contains_ref r.counter h1
         /\ contains_ref w.log h1
         /\ sel h1 w.counter = 0
         /\ sel h1 r.counter = 0
         /\ sel h1 w.log = createEmpty
         ))


