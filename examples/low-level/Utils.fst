module Utils

open FStar.SeqProperties
open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open Low.Bytes

#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let lemma_slice_sub_1 (#a:Type{hasEq a}) (s:Seq.seq a) (s':Seq.seq a) (a:nat) (b:nat{a <= b /\ b <= Seq.length s /\ b <= Seq.length s'}) : Lemma
  (requires (s == s'))
  (ensures  (Seq.slice s a b == Seq.slice s' a b))
  [SMTPat (Seq.slice s a b); SMTPat (Seq.slice s' a b)]
  = ()

val lemma_slice_0: #a:Type -> s:Seq.seq a -> i:nat -> j:nat{i <= j && j <= Seq.length s} -> Lemma
  (requires (True))
  (ensures  (forall (k:nat). {:pattern (Seq.index (Seq.slice s i j) k)} k < j - i ==> Seq.index (Seq.slice s i j) k == Seq.index s (k+i)))
let lemma_slice_0 #a s i j = ()

let lemma_slice_sub_2 s (a:nat) (b:nat) (a':nat) (b':nat{b - a >= b' /\ a <= b /\ b <= Seq.length s /\ a' <= b' /\ a + b' <= Seq.length s}) : Lemma
  (requires (True))
  (ensures  (Seq.length (Seq.slice s a b) = b - a
    /\ Seq.slice (Seq.slice s a b) a' b' == Seq.slice s (a+a') (a+b') ))
  [SMTPat (Seq.slice (Seq.slice s a b) a' b')]
  = Seq.lemma_len_slice s a b;
    Seq.lemma_len_slice (Seq.slice s a b) a' b';
    Seq.lemma_len_slice s (a+a') (a+b');
    let s1 = Seq.slice s a b in
    let s2 = Seq.slice s1 a' b' in
    let s3 = Seq.slice s (a+a') (a+b') in
    lemma_slice_0 s a b;
    lemma_slice_0 s1 a' b';
    lemma_slice_0 s (a+a') (a+b');
    assert(forall (i:nat). i < b' - a' ==> Seq.index s2 i == Seq.index s (i+a+a'));
    Seq.lemma_eq_intro s2 s3;
    Seq.lemma_eq_elim s2 s3

let lemma_equal s s' (i:nat) : Lemma
  (requires (s == s' /\ i < Seq.length s))
  (ensures  (Seq.length s = Seq.length s' /\ i < Seq.length s /\ Seq.index s i == Seq.index s' i))
  [SMTPat (Seq.index s i); SMTPat (s == s')]
  = ()

val xor_seq_bytes: s1:Seq.seq UInt8.t -> s2:Seq.seq UInt8.t -> len:nat -> Pure (Seq.seq UInt8.t)
  (requires (len <= Seq.length s1 /\ len <= Seq.length s2))
  (ensures  (fun z -> Seq.length z = len))
  (decreases len)
let rec xor_seq_bytes s1 s2 len =
  if len = 0 then Seq.createEmpty #UInt8.t
  else begin
    let i = len - 1 in
    let s1i = Seq.index s1 i in
    let s2i = Seq.index s2 i in
    Seq.append (xor_seq_bytes s1 s2 i) (Seq.create 1 (UInt8.logxor s1i s2i))
  end

#set-options "--max_fuel 1 --initial_fuel 1"

val xor_seq_bytes_lemma_0: s1:Seq.seq UInt8.t -> s2:Seq.seq UInt8.t -> s1':Seq.seq UInt8.t -> s2':Seq.seq UInt8.t -> len:nat -> Lemma
  (requires (Seq.length s1 >= len /\ Seq.length s2 >= len /\ Seq.length s1' >= len /\ Seq.length s2' >= len
    /\ Seq.slice s1 0 len == Seq.slice s1' 0 len /\ Seq.slice s2 0 len == Seq.slice s2' 0 len))
  (ensures  (Seq.length s1 >= len /\ Seq.length s2 >= len /\ Seq.length s1' >= len /\ Seq.length s2' >= len
    /\ xor_seq_bytes s1 s2 len == xor_seq_bytes s1' s2' len))
let rec xor_seq_bytes_lemma_0 s1 s2 s1' s2' len =
  match len with 
  | 0 -> ()
  | _ -> 
    lemma_slice_sub_2 s1 0 len 0 (len-1);
    lemma_slice_sub_2 s2 0 len 0 (len-1);
    xor_seq_bytes_lemma_0 s1 s2 s1' s2' (len-1);
    assert(Seq.index (Seq.slice s1 0 len) (len-1) = Seq.index (Seq.slice s1' 0 len) (len-1));
    assert(Seq.index (Seq.slice s2 0 len) (len-1) = Seq.index (Seq.slice s2' 0 len) (len-1))

#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val lemma_slice_append: #a:Type -> s:Seq.seq a -> i:nat{i < Seq.length s} -> Lemma
  (Seq.slice s 0 (i+1) == Seq.append (Seq.slice s 0 i) (Seq.create 1 (Seq.index s i)))
let lemma_slice_append #a s i = 
  Seq.lemma_eq_intro (Seq.slice s 0 (i+1)) (Seq.append (Seq.slice s 0 i) (Seq.create 1 (Seq.index s i)))

val lemma_seq_upd: #a:Type -> s:Seq.seq a -> s':Seq.seq a -> s'':Seq.seq a -> i:nat{i < Seq.length s} -> oi:a -> Lemma
  (requires (s' == Seq.upd s i oi /\ Seq.length s'' >= Seq.length s /\ Seq.slice s'' i (Seq.length s) == Seq.slice s' i (Seq.length s)))
  (ensures  (Seq.length s'' >= Seq.length s /\ Seq.slice s'' (i+1) (Seq.length s) == Seq.slice s (i+1) (Seq.length s)))
let lemma_seq_upd #a s s' s'' i oi =
  Seq.lemma_eq_intro (Seq.slice s' (i+1) (Seq.length s)) (Seq.slice s (i+1) (Seq.length s));
  assert(Seq.slice s'' (i+1) (Seq.length s) == Seq.slice (Seq.slice s'' i (Seq.length s)) 1 (Seq.length s - i));
  assert(Seq.slice s' (i+1) (Seq.length s) == Seq.slice (Seq.slice s' i (Seq.length s)) 1 (Seq.length s - i));
  Seq.lemma_eq_intro (Seq.slice s'' (i+1) (Seq.length s)) (Seq.slice s' (i+1) (Seq.length s))

#reset-options "--z3timeout 20"
#set-options "--max_fuel 1 --initial_fuel 1"

val xor_bytes_inplace_lemma: h0:mem -> h1:mem -> h2:mem -> output:bytes -> in1:bytes -> i:nat -> oi:UInt8.t -> Lemma
  (requires (live h0 output /\ live h1 output /\ live h2 output /\ live h0 in1 /\ live h1 in1
    /\ length output >= i + 1 /\ length in1 >= i + 1
    /\ oi = UInt8.logxor (Seq.index (to_seq8 h0 output) i) (Seq.index (to_seq8 h0 in1) i)
    /\ to_seq8 h1 output == Seq.upd (to_seq8 h0 output) (i) (oi)
    /\ to_seq8 h1 in1 == to_seq8 h0 in1
    /\ Seq.slice (to_seq8 h2 output) 0 (i) == xor_seq_bytes (to_seq8 h1 output) (to_seq8 h1 in1) (i)
    /\ Seq.slice (to_seq8 h2 output) (i) (length output) == 
	Seq.slice (to_seq8 h1 output) (i) (length output) ))
  (ensures  (live h0 output /\ live h2 output /\ live h0 in1
    /\ length output >= i + 1 /\ length in1 >= i + 1
    /\ Seq.slice (to_seq8 h2 output) (i+1) (length output) == Seq.slice (to_seq8 h0 output) (i+1) (length output)
    /\ Seq.slice (to_seq8 h2 output) 0 (i + 1) == xor_seq_bytes (to_seq8 h0 output) (to_seq8 h0 in1) (i+1) ))
    //Seq.append (xor_seq_bytes (to_seq8 h0 output) (to_seq8 h0 in1) (i)) (Seq.create 1 oi) ))
let xor_bytes_inplace_lemma h0 h1 h2 output in1 i oi =
  lemma_seq_upd (to_seq8 h0 output) (to_seq8 h1 output) (to_seq8 h2 output) i oi;
  assume (Seq.slice (to_seq8 h1 output) 0 i == Seq.slice (to_seq8 h0 output) 0 i);
  xor_seq_bytes_lemma_0 (to_seq8 h1 output) (to_seq8 h1 in1) (to_seq8 h0 output) (to_seq8 h0 in1) i;
  assert(Seq.slice (to_seq8 h2 output) 0 i == xor_seq_bytes (to_seq8 h0 output) (to_seq8 h0 in1) i);
  lemma_slice_append (to_seq8 h2 output) i;
  assert(Seq.slice (to_seq8 h2 output) 0 (i+1) == Seq.append (xor_seq_bytes (to_seq8 h0 output) (to_seq8 h0 in1) i) (Seq.create 1 (Seq.index (to_seq8 h2 output) i)));
  assert(Seq.index (Seq.slice (to_seq8 h1 output) i (length output)) 0 = oi);
  assert(Seq.index (Seq.slice (to_seq8 h2 output) i (length output)) 0 = oi);
  assert(Seq.index (to_seq8 h2 output) i = oi);
  assert(Seq.append (xor_seq_bytes (to_seq8 h0 output) (to_seq8 h0 in1) i) (Seq.create 1 oi)
		    == xor_seq_bytes (to_seq8 h0 output) (to_seq8 h0 in1) (i+1) )

#reset-options "--z3timeout 20"

val xor_bytes_inplace: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:UInt32.t{UInt32.v len <= length output /\ UInt32.v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ modifies_1 output h0 h1
    /\ Seq.slice (to_seq8 h1 output) 0 (UInt32.v len) ==
      	xor_seq_bytes (to_seq8 h0 output) (to_seq8 h0 in1) (UInt32.v len)
    /\ Seq.slice (to_seq8 h1 output) (UInt32.v len) (length output) ==
	Seq.slice (to_seq8 h0 output) (UInt32.v len) (length output) ))
let rec xor_bytes_inplace output in1 len =
  if UInt32.eq len 0ul then
    let h = HST.get() in
    Seq.lemma_eq_intro (Seq.slice (to_seq8 h output) 0 0) (Seq.createEmpty #UInt8.t)
  else
    begin
      let h0 = HST.get() in
      let i    = len -^ 1ul in
      let in1i = read_8 in1 i in
      let oi   = read_8 output i in
      let oi   = UInt8.logxor oi in1i in
      write_8 output i oi;
      let h1 = HST.get() in      
      cut(to_seq8 h1 output == Seq.upd (to_seq8 h0 output) (UInt32.v i) (oi));
      cut(to_seq8 h1 in1 == to_seq8 h0 in1);
      xor_bytes_inplace output in1 i;
      let h2 = HST.get() in
      cut(Seq.slice (to_seq8 h2 output) 0 (UInt32.v i) == xor_seq_bytes (to_seq8 h1 output) (to_seq8 h1 in1) (UInt32.v i));
	cut(Seq.slice (to_seq8 h2 output) (UInt32.v i) (length output) == Seq.slice (to_seq8 h1 output) (UInt32.v i) (length output));
      xor_bytes_inplace_lemma h0 h1 h2 output in1 (UInt32.v i) oi
    end
