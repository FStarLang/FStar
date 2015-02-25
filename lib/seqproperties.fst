module SeqProperties
open Seq

let rec lemma_append_count lo hi =
  if lo.length = 0
  then cut (Eq (Seq.append lo hi) hi)
  else (cut (Eq (Seq.cons (head lo) (Seq.append (tail lo) hi))
                (Seq.append lo hi));
        lemma_append_count (tail lo) hi;
        let tl_l_h = Seq.append (tail lo) hi in
        let lh = Seq.cons (head lo) tl_l_h in
        cut (Eq (tail lh) tl_l_h))

let lemma_append_count_aux x lo hi = lemma_append_count lo hi

let lemma_mem_inversion s = ()

let rec lemma_mem_count s f =
  if s.length = 0
  then ()
  else (cut (forall (i:nat{i<length (tail s)}). index (tail s) i = index s (i + 1));
        lemma_mem_count (tail s) f)

let lemma_count_slice s i =
  cut (Eq s (append (slice s 0 i) (slice s i s.length)));
  lemma_append_count (slice s 0 i) (slice s i s.length)


