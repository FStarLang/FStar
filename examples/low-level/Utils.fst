module Utils

open FStar.Seq
open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
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
  if len = 0 then Seq.empty #UInt8.t
  else begin
    let i = len - 1 in
    let s1i = Seq.index s1 i in
    let s2i = Seq.index s2 i in
    Seq.append (xor_seq_bytes s1 s2 i) (Seq.create 1 (UInt8.logxor s1i s2i))
  end

val f_seq: #a:Type -> f:(a -> a -> Tot a) -> s1:Seq.seq a -> s2:Seq.seq a -> len:nat -> Pure (Seq.seq a)
  (requires (len <= Seq.length s1 /\ len <= Seq.length s2))
  (ensures  (fun z -> Seq.length z = len))
  (decreases len)
let rec f_seq #a f s1 s2 len =
  if len = 0 then Seq.empty #a
  else begin
    let i = len - 1 in
    let s1i = Seq.index s1 i in
    let s2i = Seq.index s2 i in
    Seq.append (f_seq f s1 s2 i) (Seq.create 1 (f s1i s2i))
  end

#set-options "--max_fuel 1 --initial_fuel 1"

val f_seq_lemma_0: #a:Type -> f:(a -> a -> Tot a) -> s1:Seq.seq a -> s2:Seq.seq a -> s1':Seq.seq a -> s2':Seq.seq a -> len:nat -> Lemma
  (requires (Seq.length s1 >= len /\ Seq.length s2 >= len /\ Seq.length s1' >= len /\ Seq.length s2' >= len
    /\ Seq.slice s1 0 len == Seq.slice s1' 0 len /\ Seq.slice s2 0 len == Seq.slice s2' 0 len))
  (ensures  (Seq.length s1 >= len /\ Seq.length s2 >= len /\ Seq.length s1' >= len /\ Seq.length s2' >= len
    /\ f_seq f s1 s2 len == f_seq f s1' s2' len))
let rec f_seq_lemma_0 #a f s1 s2 s1' s2' len =
  match len with 
  | 0 -> ()
  | _ -> 
    lemma_slice_sub_2 s1 0 len 0 (len-1);
    lemma_slice_sub_2 s2 0 len 0 (len-1);
    f_seq_lemma_0 #a f s1 s2 s1' s2' (len-1);
    assert(Seq.index (Seq.slice s1 0 len) (len-1) == Seq.index (Seq.slice s1' 0 len) (len-1));
    assert(Seq.index (Seq.slice s2 0 len) (len-1) == Seq.index (Seq.slice s2' 0 len) (len-1))

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

val f_seq_inplace_lemma: h0:mem -> h1:mem -> h2:mem -> output:bytes -> in1:bytes -> i:nat -> oi:UInt8.t -> f:(UInt8.t -> UInt8.t -> Tot UInt8.t) -> Lemma
  (requires (live h0 output /\ live h1 output /\ live h2 output /\ live h0 in1 /\ live h1 in1
    /\ length output >= i + 1 /\ length in1 >= i + 1
    /\ oi = f (Seq.index (to_seq8 h0 output) i) (Seq.index (to_seq8 h0 in1) i)
    /\ to_seq8 h1 output == Seq.upd (to_seq8 h0 output) (i) (oi)
    /\ to_seq8 h1 in1 == to_seq8 h0 in1
    /\ Seq.slice (to_seq8 h2 output) 0 (i) == f_seq f (to_seq8 h1 output) (to_seq8 h1 in1) (i)
    /\ Seq.slice (to_seq8 h2 output) (i) (length output) == 
	Seq.slice (to_seq8 h1 output) (i) (length output) ))
  (ensures  (live h0 output /\ live h2 output /\ live h0 in1
    /\ length output >= i + 1 /\ length in1 >= i + 1
    /\ Seq.slice (to_seq8 h2 output) (i+1) (length output) == Seq.slice (to_seq8 h0 output) (i+1) (length output)
    /\ Seq.slice (to_seq8 h2 output) 0 (i + 1) == f_seq f (to_seq8 h0 output) (to_seq8 h0 in1) (i+1) ))

let f_seq_inplace_lemma h0 h1 h2 output in1 i oi f =
  lemma_seq_upd (to_seq8 h0 output) (to_seq8 h1 output) (to_seq8 h2 output) i oi;
  assume (Seq.slice (to_seq8 h1 output) 0 i == Seq.slice (to_seq8 h0 output) 0 i);
  f_seq_lemma_0 f (to_seq8 h1 output) (to_seq8 h1 in1) (to_seq8 h0 output) (to_seq8 h0 in1) i;
  assert(Seq.slice (to_seq8 h2 output) 0 i == f_seq f (to_seq8 h0 output) (to_seq8 h0 in1) i);
  lemma_slice_append (to_seq8 h2 output) i;
  assert(Seq.slice (to_seq8 h2 output) 0 (i+1) == Seq.append (f_seq f (to_seq8 h0 output) (to_seq8 h0 in1) i) (Seq.create 1 (Seq.index (to_seq8 h2 output) i)));
  assert(Seq.index (Seq.slice (to_seq8 h1 output) i (length output)) 0 = oi);
  assert(Seq.index (Seq.slice (to_seq8 h2 output) i (length output)) 0 = oi);
  assert(Seq.index (to_seq8 h2 output) i = oi);
  assert(Seq.append (f_seq f (to_seq8 h0 output) (to_seq8 h0 in1) i) (Seq.create 1 oi)
		    == f_seq f (to_seq8 h0 output) (to_seq8 h0 in1) (i+1) )

val f_seq_inplace_lemma': #a:Type -> #b:Type -> 
  h0:mem -> h1:mem -> h2:mem -> output:b -> in1:b -> i:nat -> oi:a -> 
  pre:(mem -> b -> Type) -> to_seq:(h:mem -> x:b{pre h x} -> GTot (Seq.seq a)) -> 
  f:(a -> a -> Tot a) -> Lemma
  (requires (pre h0 output /\ pre h0 output /\ pre h1 output /\ pre h2 output /\ pre h0 in1 /\ pre h1 in1
    /\ Seq.length (to_seq h0 output) >= i + 1 /\ Seq.length (to_seq h0 in1) >= i + 1
    /\ Seq.length (to_seq h1 output) = Seq.length (to_seq h0 output) /\ Seq.length (to_seq h1 in1) = Seq.length (to_seq h0 in1)
    /\ Seq.length (to_seq h2 output) = Seq.length (to_seq h0 output)
    /\ oi == f (Seq.index (to_seq h0 output) i) (Seq.index (to_seq h0 in1) i)
    /\ to_seq h1 output == Seq.upd (to_seq h0 output) (i) (oi)
    /\ to_seq h1 in1 == to_seq h0 in1
    /\ Seq.slice (to_seq h2 output) 0 (i) == f_seq f (to_seq h1 output) (to_seq h1 in1) (i)
    /\ Seq.slice (to_seq h2 output) (i) (Seq.length (to_seq h0 output)) == 
	Seq.slice (to_seq h1 output) (i) (Seq.length (to_seq h0 output)) ))
  (ensures  (pre h0 output /\ pre h2 output /\ pre h0 in1
    /\ Seq.length (to_seq h0 output) >= i + 1 /\ Seq.length (to_seq h0 in1) >= i + 1
    /\ Seq.length (to_seq h2 output) = Seq.length (to_seq h0 output)
    /\ Seq.slice (to_seq h2 output) (i+1) (Seq.length (to_seq h2 output)) == Seq.slice (to_seq h0 output) (i+1) (Seq.length (to_seq h0 output))
    /\ Seq.slice (to_seq h2 output) 0 (i + 1) == f_seq f (to_seq h0 output) (to_seq h0 in1) (i+1) ))
let f_seq_inplace_lemma' #a #b h0 h1 h2 output in1 i oi pre to_seq f =
  lemma_seq_upd (to_seq h0 output) (to_seq h1 output) (to_seq h2 output) i oi;
  assume (Seq.slice (to_seq h1 output) 0 i == Seq.slice (to_seq h0 output) 0 i);
  f_seq_lemma_0 f (to_seq h1 output) (to_seq h1 in1) (to_seq h0 output) (to_seq h0 in1) i;
  assert(Seq.slice (to_seq h2 output) 0 i == f_seq f (to_seq h0 output) (to_seq h0 in1) i);
  lemma_slice_append (to_seq h2 output) i;
  assert(Seq.slice (to_seq h2 output) 0 (i+1) == Seq.append (f_seq f (to_seq h0 output) (to_seq h0 in1) i) (Seq.create 1 (Seq.index (to_seq h2 output) i)));
  assert(Seq.index (Seq.slice (to_seq h1 output) i (Seq.length (to_seq h0 output))) 0 == oi);
  assert(Seq.index (Seq.slice (to_seq h2 output) i (Seq.length (to_seq h0 output))) 0 == oi);
  assert(Seq.index (to_seq h2 output) i == oi);
  assert(Seq.append (f_seq f (to_seq h0 output) (to_seq h0 in1) i) (Seq.create 1 oi)
		    == f_seq f (to_seq h0 output) (to_seq h0 in1) (i+1) )

#reset-options "--z3timeout 100"

val xor_bytes_inplace: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:UInt32.t{UInt32.v len <= length output /\ UInt32.v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ modifies_1 output h0 h1
    /\ Seq.slice (to_seq8 h1 output) 0 (UInt32.v len) ==
      	f_seq UInt8.logxor (to_seq8 h0 output) (to_seq8 h0 in1) (UInt32.v len)
    /\ Seq.slice (to_seq8 h1 output) (UInt32.v len) (length output) ==
	Seq.slice (to_seq8 h0 output) (UInt32.v len) (length output) ))
let rec xor_bytes_inplace output in1 len =
  if UInt32.eq len 0ul then
    let h = ST.get() in
    Seq.lemma_eq_intro (Seq.slice (to_seq8 h output) 0 0) (Seq.empty #UInt8.t)
  else
    begin
      let h0 = ST.get() in
      let i    = len -^ 1ul in
      let in1i = read_8 in1 i in
      let oi   = read_8 output i in
      let oi   = UInt8.logxor oi in1i in
      write_8 output i oi;
      let h1 = ST.get() in      
      cut(to_seq8 h1 output == Seq.upd (to_seq8 h0 output) (UInt32.v i) (oi));
      cut(to_seq8 h1 in1 == to_seq8 h0 in1);
      xor_bytes_inplace output in1 i;
      let h2 = ST.get() in
      cut(Seq.slice (to_seq8 h2 output) 0 (UInt32.v i) == f_seq UInt8.logxor (to_seq8 h1 output) (to_seq8 h1 in1) (UInt32.v i));
      cut(Seq.slice (to_seq8 h2 output) (UInt32.v i) (length output) == Seq.slice (to_seq8 h1 output) (UInt32.v i) (length output));      
      f_seq_inplace_lemma' h0 h1 h2 output in1 (UInt32.v i) oi (fun h b -> live h b) to_seq8 UInt8.logxor
    end

#reset-options "--z3timeout 100"

val xor_u16s_inplace: output:u16s -> in1:u16s{disjoint in1 output} ->
  len:UInt32.t{UInt32.v len <= length output /\ UInt32.v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ modifies_1 output h0 h1
    /\ Seq.slice (to_seq16 h1 output) 0 (UInt32.v len) ==
      	f_seq UInt16.logxor (to_seq16 h0 output) (to_seq16 h0 in1) (UInt32.v len)
    /\ Seq.slice (to_seq16 h1 output) (UInt32.v len) (length output) ==
	Seq.slice (to_seq16 h0 output) (UInt32.v len) (length output) ))
let rec xor_u16s_inplace output in1 len =
  if UInt32.eq len 0ul then
    let h = ST.get() in
    Seq.lemma_eq_intro (Seq.slice (to_seq16 h output) 0 0) (Seq.empty #UInt16.t)
  else
    begin
      let h0 = ST.get() in
      let i    = len -^ 1ul in
      let in1i = read_16 in1 i in
      let oi   = read_16 output i in
      let oi   = UInt16.logxor oi in1i in
      write_16 output i oi;
      let h1 = ST.get() in
      cut(to_seq16 h1 output == Seq.upd (to_seq16 h0 output) (UInt32.v i) (oi));
      cut(to_seq16 h1 in1 == to_seq16 h0 in1);
      xor_u16s_inplace output in1 i;
      let h2 = ST.get() in
      cut(Seq.slice (to_seq16 h2 output) 0 (UInt32.v i) == f_seq UInt16.logxor (to_seq16 h1 output) (to_seq16 h1 in1) (UInt32.v i));
      cut(Seq.slice (to_seq16 h2 output) (UInt32.v i) (length output) == Seq.slice (to_seq16 h1 output) (UInt32.v i) (length output));
      f_seq_inplace_lemma' h0 h1 h2 output in1 (UInt32.v i) oi (fun h b -> live h b) to_seq16 UInt16.logxor
    end
