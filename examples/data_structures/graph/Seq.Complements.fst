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

let rec index_of_l_aux (#a:Type) (f:a -> bool) (s:seq a) (i:_in s)
  : Tot (option (_in s)) (decreases (length s - i))
= if f (s @^ i) then Some i else if i = length s - 1 then None else index_of_l_aux #a f s (i+1)

let index_of_l (#a:Type) (f:a -> bool) (s:seq a) : option (_in s) =
  if length s = 0 then None else index_of_l_aux #a f s (0 <: _in s)

let rec index_of_l_aux_spec (#a:Type) (f:a -> bool) (s:seq a) (i:_in s) :
  Lemma (requires (forall (j:_in s{j < i}). not (f (s @^ j))))
    (ensures (let r = index_of_l_aux f s i in
    (forall (i:_in s). (~(Some? r) \/ i < Some?.v r) ==>  not (f (s @^ i))) /\
      (Some? r ==> f (s @^ Some?.v r))))
    (decreases (length s - i))
= if f (s @^ i) then () else if i = length s - 1 then () else index_of_l_aux_spec #a f s (i+1)

let rec index_of_l_spec (#a:Type) (f:a -> bool) (s:seq a) :
    Lemma (let r = index_of_l f s in
    (forall (i:_in s). (~(Some? r) \/ i < Some?.v r) ==> not (f (s @^ i))) /\
      (Some? r ==> f (s @^ Some?.v r)))
= if length s = 0 then ()
  else index_of_l_aux_spec f s 0


let rec none_count_zero (#a:eqtype) (e:a) (s:seq a)
  : Lemma (requires (forall (i:_in s). not (e = s @^ i))) (ensures (count e s == 0)) (decreases (length s))
= if length s = 0 then ()
  else
    let s' = tail s in
    assert (not (e = s @^ 0)) ;
    assert (forall (i:_in (tail s)). not (e = s @^ (i+1))) ;
    none_count_zero #a e (tail s)

let index_of_l_count (#a:eqtype) (e:a) (s:seq a)
  : Lemma (match index_of_l (fun x -> x = e) s with | None -> count e s == 0 | Some i0 -> s @^ i0 = e)
= let f x = x = e in
  index_of_l_spec f s ;
  match index_of_l f s with
  | None -> none_count_zero e s
  | Some i0 -> ()
