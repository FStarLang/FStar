module OPLSS
module UInt8 = FStar.UInt8
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer
let bytes = Seq.seq UInt8.t
let lbytes l = b:bytes{Seq.length b = l}

assume //demo scaffolding
val random (l:nat) : EXT (lbytes l)

assume //demo scaffolding
val byte_of_int: n:nat{n < 256} -> Tot UInt8.t

assume //demo scaffolding
val xor: l:nat -> lbytes l -> lbytes l -> Tot (lbytes l)

open FStar.Seq

val auto_lemma_mem_snoc : #a:eqtype -> s:Seq.seq a -> x:a -> y:a ->
   Lemma
     (ensures (mem y (snoc s x) <==> mem y s \/ x=y))
     [SMTPat (mem y (snoc s x))]
let auto_lemma_mem_snoc #a s x y = Seq.lemma_mem_snoc s x
