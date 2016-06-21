module FStar.Buffer.Op

open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Buffer

#reset-options "--z3timeout 10"
#set-options "--lax"

(* TODO: simplify, add triggers ? *)
private val blit_aux: #a:Type -> b:buffer a -> idx_b:u32 -> 
  b':buffer a -> idx_b':u32 -> len:u32{v idx_b+v len<=length b/\v idx_b'+v len<= length b'} -> 
  ctr:u32{v ctr <= v len} ->  STL unit
  (requires (fun h -> live h b /\ live h b' /\ disjoint b b'
    /\ (forall (i:nat). i < v ctr ==> get h b (v idx_b+i) = get h b' (v idx_b'+i)) ))
  (ensures (fun h0 _ h1 -> live h1 b /\ live h1 b'  /\ live h0 b /\ live h0 b' 
    /\ disjoint b b' /\ length b >= v idx_b+v len /\ length b' >= v idx_b'+v len
    /\ modifies_one (frameOf b') h0 h1
    /\ modifies_buf (frameOf b') (only b') h0 h1    
    /\ (forall (i:nat). {:pattern (get h1 b' (v idx_b'+i))} i < v len 
	==> get h0 b (v idx_b+i) = get h1 b' (v idx_b'+i))
    /\ (forall (i:nat). {:pattern (get h1 b' i)} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) 
	==> get h1 b' i = get h0 b' i) ))
let rec blit_aux #a b idx_b b' idx_b' len ctr = 
  let h0 = HST.get() in
  if (len -^ ctr) =^ (uint_to_t 0) then ()
  else 
  begin
    let bctr = index b (idx_b +^ ctr) in
    upd b' (idx_b' +^ ctr) bctr;
    let h1 = HST.get() in
    // JK: required for verfication but breaks extraction (infinite loop)
    (* equal_lemma (frameOf b') h0 h1 b (only b'); *)
    cut (forall (i:nat). {:pattern (get h1 b' i)} (i <> v idx_b'+v ctr /\ i < length b') ==> get h1 b' i = get h0 b' i); 
    cut (modifies_one (frameOf b') h0 h1);
    cut (modifies_buf (frameOf b') (only b') h0 h1);
    blit_aux b idx_b b' idx_b' len (ctr +^ (uint_to_t 1)); 
    let h2 = HST.get() in
    // JK: required for verfication but breaks extraction (infinite loop)
    (* equal_lemma (frameOf b') h1 h2 b (only b'); *)
    cut (live h2 b /\ live h2 b');
    cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h1 b (v idx_b+i));
    cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h0 b (v idx_b+i));
    cut (forall (i:nat). {:pattern (get h2 b')} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) ==> get h2 b' i = get h1 b' i);
    cut (modifies_one (frameOf b') h1 h2);
    cut (modifies_buf (frameOf b') (only b') h1 h2);
    cut (modifies_one (frameOf b') h0 h2);
    cut (modifies_buf (frameOf b') (only b') h0 h2);
    cut (modifies_ref (frameOf b') !{as_ref b'} h0 h1); (* Trigger *)
    cut (modifies_ref (frameOf b') !{as_ref b'} h1 h2); (* Trigger *)
    cut (modifies_ref (frameOf b') !{as_ref b'} h0 h2) (* Trigger *)
  end

#reset-options

val blit: #t:Type -> a:buffer t -> idx_a:u32{v idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:u32{v idx_b <= length b} -> len:u32{v idx_a+v len <= length a /\ v idx_b+v len <= length b} -> STL unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a
      /\ (forall (i:nat). {:pattern (get h1 b (v idx_b+i))} i < v len ==> get h1 b (v idx_b+i) = get h0 a (v idx_a+i))
      /\ (forall (i:nat). {:pattern (get h1 b i)} ((i >= v idx_b + v len /\ i < length b) \/ i < v idx_b) ==> get h1 b i = get h0 b i)
      /\ modifies_one (frameOf b) h0 h1
      /\ modifies_buf (frameOf b) (only b) h0 h1 ))
let blit #t a idx_a b idx_b len = blit_aux a idx_a b idx_b len (uint_to_t 0)

val split: #a:Type -> a:buffer t -> i:u32{v i <= length a} -> ST (buffer t * buffer t)
    (requires (fun h -> live h a))
    (ensures (fun h0 b h1 -> live h1 (fst b) /\ live h1 (snd b) /\ h1 == h0 /\ idx (fst b) = idx a 
      /\ idx (snd b) = idx a + v i /\ length (fst b) = v i /\ length (snd b) = length a - v i 
      /\ disjoint (fst b) (snd b)  /\ content (fst b) = content a /\ content (snd b) = content a))
let split #t a i = 
  let a1 = sub a (uint_to_t 0) i in let a2 = sub a i (a.length -^ i) in a1, a2

val offset: #a:Type -> a:buffer t -> i:u32{v i <= length a} -> STL (buffer t)
  (requires (fun h -> live h a))
  (ensures (fun h0 a' h1 -> h0 == h1 /\ content a' = content a /\ idx a' = idx a + v i /\ length a' = length a - v i))
let offset #t a i = {content = a.content; idx = i +^ a.idx; length = a.length -^ i}

private val of_seq_aux: #a:Type -> s:bounded_seq a -> l:u32{v l = Seq.length s} -> ctr:u32{v ctr <= v l} -> b:buffer a{idx b = 0 /\ length b = v l} -> STL unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b 
      /\ (forall (i:nat). {:pattern (get h1 b i)} i < v ctr ==> get h1 b i = Seq.index s i)
      /\ (forall (i:nat). {:pattern (get h1 b i)} i >= v ctr /\ i < length b ==> get h1 b i = get h0 b i)
      /\ modifies_one (frameOf b) h0 h1
      /\ modifies_buf (frameOf b) (only b) Set.empty h0 h1))
let rec of_seq_aux #a s l ctr b =
  if ctr =^ (uint_to_t 0) then ()
  else 
  begin
    let j = ctr -^ (uint_to_t 1) in 
    upd b j (Seq.index s (v j)); (* JK: no concrete implementation of Seq for now as far as I know *)
    of_seq_aux s l j b	 
  end

val of_seq: #a:Type -> s:seq a -> l:u32{v l = Seq.length s /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> idx b = 0 /\ length b = v l /\ ~(contains h0 b) /\ live h1 b
    /\ frameOf b = h1.tip
    /\ modifies_one (frameOf b) h0 h1
    /\ modifies_buf (frameOf b) Set.empty Set.empty h0 h1
    /\ (forall (i:nat). {:pattern (get h1 b i)} i < v l ==> get h1 b i = Seq.index s i) ))
let of_seq #a s l =
  let init = Seq.index s 0 in
  let h0 = HST.get () in
  let b = create #a init l in 
  let h1 = HST.get () in
  of_seq_aux s l l b; 
  let h2 = HST.get () in
  b

val clone: #a:Type ->  b:buffer a -> l:u32{length b >= v l /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> ~(contains h0 b')
	      /\ live h0 b
	      /\ live h1 b'
	      /\ idx b' = 0 
	      /\ length b' = v l 
	      /\ (forall (i:nat). {:pattern (get h1 b' i)} i < v l ==> get h1 b' i = get h0 b i)
	      /\ modifies_one (frameOf b') h0 h1
	      /\ modifies_buf (frameOf b') Set.empty Set.empty h0 h1 ))
let clone #a b l =
  let (init:a) = index b (uint_to_t 0) in 
  let (b':buffer a) = create init l in 
  blit b (uint_to_t 0) b' (uint_to_t 0) l; 
  b'
