module FStar.DM4F.Heap.Random

(***** Random tape *****)

open FStar.Seq

let size = 10

assume val q: pos

let elem = n:nat{n < q}

abstract type id : eqtype = i:nat{i < size}
abstract type tape : eqtype = h:seq elem{length h == size}

abstract let to_id (n:nat{n < size}) : id = n

abstract val incrementable: id -> bool
let incrementable (i:id) = i + 1 < size

abstract let incr (i:id{incrementable i}) : id = to_id (i + 1)

abstract let index (h:tape) (i:id) : Tot elem = index h i
let sel = index
abstract let upd (h:tape) (i:id) (x:elem) : Tot tape = upd h i x

abstract let create (x:elem) : Tot tape = create #elem size x

abstract val equal: tape -> tape -> GTot Type0
let equal (t1:tape) (t2:tape) = Seq.equal t1 t2

abstract val lemma_eq_intro: s1:tape -> s2:tape -> Lemma
  (requires ((forall (i:id).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)))
  (ensures (equal s1 s2))
  [SMTPat (equal s1 s2)]
let lemma_eq_intro s1 s2 =
  assert (forall (i:id). index s1 i == Seq.index s1 i);
  assert (forall (i:id). index s2 i == Seq.index s2 i);
  Seq.lemma_eq_intro #elem s1 s2

abstract val lemma_eq_elim: s1:tape -> s2:tape -> Lemma
  (requires (equal s1 s2))
  (ensures (s1==s2))
  [SMTPat (equal s1 s2)]
let lemma_eq_elim s1 s2 = ()

abstract val lemma_index_upd1: s:tape -> n:id -> v:elem -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v))
  [SMTPat (index (upd s n v) n)]
let lemma_index_upd1 s n v = lemma_index_upd1 #elem s n v

abstract val lemma_index_upd2: s:tape -> n:id -> v:elem -> i:id{i<>n} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i))
  [SMTPat (index (upd s n v) i)]
let lemma_index_upd2 s n v i = lemma_index_upd2 #elem s n v i

abstract val lemma_index_create: v:elem -> i:id -> Lemma
  (requires True)
  (ensures (index (create v) i == v))
  [SMTPat (index (create v) i)]
let lemma_index_create v i = lemma_index_create #elem size v i
