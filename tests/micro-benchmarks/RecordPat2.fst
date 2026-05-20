module RecordPat2

class deq (a:Type) = {
  ( =? ) : a -> a -> bool;

  eq_sound :
    (x:a) -> (y:a) ->
      Lemma (requires x =? y)
            (ensures x == y)
            [SMTPat (x =? y)]
}

let test0 #t {| deq t |} (x y : t) =
  if x =? y then (
    eq_sound x y;
    assert (x == y)
  )

let test1 #t {| d : deq t |} (x y : t) =
  if d.op_Equals_Question x y then
    assert (x == y)

let test2 #t {| d : deq t |} (x y : t) =
  let _ = d.op_Equals_Question x y in
  if x =? y then
    assert (x == y)

let test3 #t {| d : deq t |} (x y : t) =
  if x =? y then
    assert (x == y)
