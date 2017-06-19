module Seq.Complements

open FStar.Seq

let _in (s:seq 'a) = k:nat{k < length s}
let ( @^ ) (s:seq 'a) (i:_in s) : 'a = index s i
let snoc (s:seq 'a) (x:'a) = s `append` (create 1 x)

let rec index_of_aux (#a:eqtype) (e:a) (s : seq a) (i : _in s)
 : Pure (option (_in s)) 
  (requires (count e (slice s 0 i) == 0)) 
  (ensures fun i' -> match i' with | None -> count e s == 0 | Some i0 -> s @^ i0 == e)
  (decreases (length s - i))
= if s @^ i = e
  then Some i
  else begin 
    lemma_eq_elim (slice s 0 (i + 1)) (append (slice s 0 i) (slice s i (i + 1)));
    lemma_append_count_aux e (slice s 0 i) (slice s i (i + 1));
    assert(count e (slice s 0 (i+1)) == 0);
    if i = length s - 1 then
      (
        lemma_eq_elim s (slice s 0 (length s));
        assert (slice s 0 (length s) == s) ; None
      )
    else
      index_of_aux e s (i + 1)
  end

let index_of(#a:eqtype) (e:a) (s : seq a)
 : Pure (option (_in s)) 
  (requires (True))
  (ensures fun i' -> match i' with | None -> count e s == 0 | Some i0 -> s @^ i0 == e)
  = if length s = 0 then None else index_of_aux e s 0
