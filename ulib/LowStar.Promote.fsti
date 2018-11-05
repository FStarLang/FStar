module LowStar.Promote

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.ConstantTime.Integers

open LowStar.Buffer

module CT = FStar.ConstantTime.Integers

type pub (sw:sw) = t (Secret lo sw)
type sec (sw:sw) = t (Secret hi sw)

val declassifiable: #sw:sw -> Seq.seq (sec sw) -> buffer (sec sw) -> buffer (pub sw) -> Type0

val map:#a:Type -> #b:Type
  -> f:(a -> b)
  -> s1:Seq.seq a
  -> s2:Seq.seq b{Seq.length s1 == Seq.length s2 /\
                 (forall (i:nat{i < Seq.length s1}).{:pattern (Seq.index s2 i)} 
                   Seq.index s2 i == f (Seq.index s1 i))}

val promote (#sw:sw) (b:buffer (pub sw)) : Stack (buffer (sec sw)) 
  (requires fun h0 -> live h0 b) 
  (ensures  fun h0 b' h1 -> 
    h0 == h1 /\
    live h1 b' /\
    as_seq h1 b' == map (fun x -> promote #_ #lo x hi) (as_seq h0 b) /\
    declassifiable (as_seq h1 b') b' b)

val demote (#sw:sw) 
  (b':buffer (sec sw)) 
  (b :buffer (pub sw)) : 
  ST unit
    (requires fun h0 -> live h0 b /\ declassifiable (as_seq h0 b') b' b)
    (ensures  fun h0 _ h1 -> 
      live h1 b /\
      as_seq h0 b' == map (fun x -> CT.promote #_ #lo x hi) (as_seq h1 b))
