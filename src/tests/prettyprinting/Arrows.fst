module Arrows

abstract
val op_At_Bar: #a: Type -> s1: array a -> s2: array a ->
  ST (array a)
    (requires (fun h -> contains h s1 /\ contains h s2))
    (ensures
      (fun h0 s h1 ->
          contains h0 s1 /\ contains h0 s2 /\ contains h1 s /\
          sel h1 s == Seq.append (sel h0 s1) (sel h0 s2) /\ modifies Set.empty h0 h1))

let op_At_Bar: #a: Type -> s1: array a -> s2: array a ->
  ST (array a)
    (requires (fun h -> contains h s1 /\ contains h s2))
    (ensures
      (fun h0 s h1 ->
          contains h0 s1 /\ contains h0 s2 /\ contains h1 s /\
          sel h1 s == Seq.append (sel h0 s1) (sel h0 s2) /\ modifies Set.empty h0 h1)) =
  let s1' = !s1 in
  let s2' = !s2 in
  ST.alloc (Seq.append s1' s2')

[@ "substitute"]
val hmac_part2: 
  mac: uint8_p{length mac = v Hash.size_hash} ->
  s5: uint8_p{length s5 = v Hash.size_block /\ disjoint s5 mac} ->
  s4: uint8_p{length s4 = v Hash.size_hash /\ disjoint s4 mac /\ disjoint s4 s5} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h s5 /\ live h s4))
    (ensures
      (fun h0 _ h1 ->
          live h1 mac /\ live h0 mac /\ live h1 s5 /\ live h0 s5 /\ live h1 s4 /\ live h0 s4 /\
          modifies_1 mac h0 h1 /\
          (reveal_sbytes (as_seq h1 mac) ==
            Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))
              ))))

[@ "substitute"]
let hmac_part2: 
  mac: uint8_p{length mac = v Hash.size_hash} ->
  s5: uint8_p{length s5 = v Hash.size_block /\ disjoint s5 mac} ->
  s4: uint8_p{length s4 = v Hash.size_hash /\ disjoint s4 mac /\ disjoint s4 s5} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h s5 /\ live h s4))
    (ensures
      (fun h0 _ h1 ->
          live h1 mac /\ live h0 mac /\ live h1 s5 /\ live h0 s5 /\ live h1 s4 /\ live h0 s4 /\
          modifies_1 mac h0 h1 /\
          (reveal_sbytes (as_seq h1 mac) ==
            Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))
              )))) = def

val last: a: int -> b: int -> Tot (array a)

