module Arrows

abstract
val op_At_Bar (#a: Type) (s1 s2: array a)
    : ST (array a)
      (requires (fun h -> contains h s1 /\ contains h s2))
      (ensures
        (fun h0 s h1 ->
            contains h0 s1 /\ contains h0 s2 /\ contains h1 s /\
            sel h1 s == Seq.append (sel h0 s1) (sel h0 s2) /\ modifies Set.empty h0 h1))

let op_At_Bar: #a: Type -> s1: array a -> s2: array a
  -> ST (array a)
      (requires (fun h -> contains h s1 /\ contains h s2))
      (ensures
        (fun h0 s h1 ->
            contains h0 s1 /\ contains h0 s2 /\ contains h1 s /\
            sel h1 s == Seq.append (sel h0 s1) (sel h0 s2) /\ modifies Set.empty h0 h1)) =
  let s1' = !s1 in
  let s2' = !s2 in
  ST.alloc (Seq.append s1' s2')

[@ "substitute"]
val hmac_part2
      (mac: uint8_p{length mac = v Hash.size_hash})
      (s5: uint8_p{length s5 = v Hash.size_block /\ disjoint s5 mac})
      (s4: uint8_p{length s4 = v Hash.size_hash /\ disjoint s4 mac /\ disjoint s4 s5})
    : Stack unit
      (requires (fun h -> live h mac /\ live h s5 /\ live h s4))
      (ensures
        (fun h0 _ h1 ->
            live h1 mac /\ live h0 mac /\ live h1 s5 /\ live h0 s5 /\ live h1 s4 /\ live h0 s4 /\
            modifies_1 mac h0 h1 /\
            (reveal_sbytes (as_seq h1 mac) ==
              Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5))
                    (reveal_sbytes (as_seq h0 s4))))))

[@ "substitute"]
let hmac_part2:
    mac: uint8_p{length mac = v Hash.size_hash} ->
    s5: uint8_p{length s5 = v Hash.size_block /\ disjoint s5 mac} ->
    s4: uint8_p{length s4 = v Hash.size_hash /\ disjoint s4 mac /\ disjoint s4 s5}
  -> Stack unit
      (requires (fun h -> live h mac /\ live h s5 /\ live h s4))
      (ensures
        (fun h0 _ h1 ->
            live h1 mac /\ live h0 mac /\ live h1 s5 /\ live h0 s5 /\ live h1 s4 /\ live h0 s4 /\
            modifies_1 mac h0 h1 /\
            (reveal_sbytes (as_seq h1 mac) ==
              Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5))
                    (reveal_sbytes (as_seq h0 s4)))))) = def

val last (a b: int) : Tot (array a)

[@ one two three four five six seven eight nine ten eleven ten eleven ten eleven ten eleven ten here
   eleven ten eleven ten eleven ten eleven]
type t =
  | A : int -> t
  | B
  | C : int -> int -> t
  | D of int

type signatureScheme =
  | RSA_PKCS1_SHA256
  | RSA_PKCS1_SHA384
  | RSA_PKCS1_SHA512
  | SIG_UNKNOWN of (codepoint:
    lbytes 2
      { let v = int_of_bytes codepoint in
        v <> 0x0401 /\ v <> 0x0501 /\ v <> 0x0601 /\ v <> 0x0403 /\ v <> 0x0503 /\ v <> 0x0603 /\
        v <> 0x0804 /\ v <> 0x0805 /\ v <> 0x0806 /\ v <> 0x0201 /\ v <> 0x0203 /\ v <> 0x0202 /\
        v <> 0x0402 /\ v <> 0x0502 /\ v <> 0x0602 /\ v <> 0xFFFF })

[@ "substitute"]
val hmac_part2
      (mac: uint8_p{length mac = v Hash.size_hash})
      (s5: uint8_p{length s5 = v Hash.size_block /\ disjoint s5 mac})
      (s4: uint8_p{length s4 = v Hash.size_hash /\ disjoint s4 mac /\ disjoint s4 s5})
    : Stack unit
      (requires (fun h -> live h mac /\ live h s5 /\ live h s4))
      (ensures
        (fun h0 _ h1 ->
            live h1 mac /\ live h0 mac /\ live h1 s5 /\ live h0 s5 /\ live h1 s4 /\ live h0 s4 /\
            modifies_1 mac h0 h1 /\
            (reveal_sbytes (as_seq h1 mac) ==
              Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5))
                    (reveal_sbytes (as_seq h0 s4))))))

abstract
val gf128_add_pure_loop (#n: pos) (a: seq (bv_t 8) {length a = n}) (b: seq (bv_t 8) {length b = n})
    : //line after Tot should actually be indented
    Tot
    (r:
      seq (bv_t 8)
        { length r = n /\
          (forall (i: nat{i < n}). equal (index r i) (logxor_vec (index a i) (index b i))) })

