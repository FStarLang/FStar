module FStar.UInt.Minus

open FStar.UInt 

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

#set-options "--z3rlimit 10"
val lemma_uint_mod: #n:pos -> a:uint_t n ->
  Lemma (a = a % pow2 n)
let lemma_uint_mod #n a = ()
#set-options "--z3rlimit 5"

val lemma_add_sub_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (add_mod (sub_mod a b) b = a)
let lemma_add_sub_cancel #n a b = 
  let ab = (a-b) % pow2 n in
  let abb = (ab + b) % pow2 n in
  let ab_mod = sub_mod a b in
  let abb_mod = add_mod ab b in
  let p = pow2 n in
  lemma_uint_mod a;
  assert (add_mod (sub_mod a b) b = add_mod ab_mod b);
  assert (add_mod ab_mod b = (ab_mod + b) % p);
  assert (add_mod ab_mod b = ((a-b) % p + b) % p);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (a-b) b p;
  assert (((a-b) + b) % p = (((a-b) % p) + b) % p);
  assert (a % p = (((a-b) % p) + b) % p)

val lemma_mod_sub_distr_l: a:int -> b:int -> p:pos -> 
  Lemma ((a - b) % p = ((a % p) - b) % p)
let lemma_mod_sub_distr_l a b p =
  let q = (a - (a % p)) / p in
  FStar.Math.Lemmas.lemma_mod_spec2 a p;
  FStar.Math.Lemmas.lemma_mod_plus (a % p - b) q p

val lemma_sub_add_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (sub_mod (add_mod a b) b = a)
let lemma_sub_add_cancel #n a b = 
  let ab = (a+b) % pow2 n in
  let abb = (ab - b) % pow2 n in
  let ab_mod = add_mod a b in
  let abb_mod = sub_mod ab b in
  let p = pow2 n in
  lemma_uint_mod a;
  lemma_mod_sub_distr_l (a+b) b p

let zero_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = Seq.append (Seq.create 1 false) a
let one_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = Seq.append (Seq.create 1 true) a

let zero_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (zero_extend_vec (to_vec a)) 
let one_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (one_extend_vec (to_vec a))

val lemma_zero_extend: #n:pos -> a:uint_t n -> 
  Lemma (zero_extend a = a)
  [SMTPat (zero_extend a)]
let lemma_zero_extend #n a = 
  let hd0 = Seq.create 1 false in
  let av = to_vec a in
  let eav = Seq.append hd0 av in
  let r = zero_extend a in
  append_lemma #1 #n hd0 av;
  assert (r = from_vec eav);
  from_vec_propriety #(n+1) eav 1;
  assert (r = a)

val lemma_one_extend: #n:pos -> a:uint_t n -> 
  Lemma (one_extend a = pow2 n + a)
  [SMTPat (one_extend a)]
let lemma_one_extend #n a = 
  let hd1 = Seq.create 1 true in
  let av = to_vec a in
  let eav = Seq.append hd1 av in
  let r = one_extend a in
  append_lemma #1 #n hd1 av;
  assert (r = from_vec eav);
  from_vec_propriety #(n+1) eav 1;
  assert (r = pow2 n + a)

val lemma_lognot_zero_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (zero_extend a) = pow2 n + (lognot #n a))
let lemma_lognot_zero_ext #n a =
  let lhs = lognot #(n+1) a in
  let rhs = pow2 n + (lognot #n a) in
  
  let av = to_vec a in
  assert (Seq.length av = n);
  let hd0 = Seq.create 1 false in
  let hd1 = Seq.create 1 true in
  let nav = to_vec (lognot a) in
  let eav = Seq.append hd0 av in
     
  append_lemma #1 #n hd0 av;
  assert (from_vec #(n+1) eav = op_Multiply (from_vec #1 hd0) (pow2 n) + from_vec av);
  assert (op_Multiply (from_vec #1 hd0) (pow2 n) = 0);
  assert (from_vec #(n+1) eav = from_vec #n av);
  assert (from_vec #(n+1) eav < pow2 n);
  
  let nav = BitVector.lognot_vec #n av in  
  let neav_r = BitVector.lognot_vec #(n+1) eav in
  let neav_l = Seq.append hd1 nav in
  append_lemma #1 #n hd1 nav;
  assert (from_vec #(n+1) neav_l = (op_Multiply (from_vec #1 hd1) (pow2 n)) + (from_vec #n nav));
  assert (op_Multiply (from_vec #1 hd1) (pow2 n) = pow2 n);
  assert (from_vec #(n+1) neav_l = pow2 n + from_vec #n nav);
  assert (pow2 n + from_vec #n nav = rhs);

  assert (forall (i:pos{i < n+1}). Seq.index neav_r i = Seq.index neav_l i);
  Seq.Base.lemma_eq_intro neav_l neav_r;
  assert (neav_l = neav_r);
  assert (from_vec neav_r = lhs)

val lemma_lognot_one_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (one_extend a) = lognot #n a)
let lemma_lognot_one_ext #n a =
  let lhs = lognot #(n+1) (one_extend a) in
  let rhs = lognot #n a in
  let av = to_vec a in
  assert (Seq.length av = n);
  let hd0 = Seq.create 1 false in
  let hd1 = Seq.create 1 true in
  let nav = to_vec (lognot #n a) in
  let eav = Seq.append hd1 av in
  append_lemma #1 #n hd1 av;
  append_lemma #1 #n hd0 nav;
  let nav = BitVector.lognot_vec #n av in
  let neav_r = BitVector.lognot_vec #(n+1) eav in
  let neav_l = Seq.append hd0 nav in
  Seq.Base.lemma_eq_elim neav_l neav_r
 
#set-options "--z3rlimit 10"
val lemma_lognot_value_mod: #n:pos -> a:uint_t n ->
  Lemma 
  (requires True)
  (ensures (lognot a = pow2 n - a - 1))
  (decreases n)
let rec lemma_lognot_value_mod #n a = 
    if n = 1 then () else
    begin
      assert (-pow2 n <= (-(a+1)) && -(a+1) < 0);
      
      let av = to_vec a in
      let hd = from_vec #1 (Seq.slice (to_vec a) 0 1) in
      let tl = from_vec #(n-1) (Seq.slice (to_vec a) 1 n) in

      assert (hd = 0 || hd = 1);
      let hdpow = op_Multiply hd (pow2 (n-1)) in
            
      from_vec_propriety (to_vec a) 1;
      assert (from_vec av = (op_Multiply 
                              (from_vec #1     (Seq.slice av 0 1)) (pow2 (n-1))) + 
                              (from_vec #(n-1) (Seq.slice av 1 n)));
      
      let ntl = lognot tl in
      lemma_lognot_value_mod #(n-1) tl;      
      assert (ntl = pow2 (n-1) - tl - 1);
      
      assert (a = hdpow + tl);
      assert (lognot a = lognot #n (hdpow + tl));
      assert (tl < pow2 (n-1));
      if hdpow = 0 then
      begin
        assert (lognot a = lognot #n tl);
        lemma_lognot_zero_ext #(n-1) tl;
        lemma_zero_extend tl
      end
      else 
      begin
        lemma_lognot_one_ext #(n-1) tl;
        lemma_one_extend tl
      end
    end

#set-options "--z3rlimit 100"
val lemma_lognot_value_zero: #n:pos -> a:uint_t n ->
  Lemma (a = 0 ==> lognot a = sub_mod (sub_mod 0 a) 1)
let lemma_lognot_value_zero #n a = 
  if a = 0 then
  begin
    let p = pow2 n in
    lemma_lognot_value_mod a;
    assert (lognot #n 0 = pow2 n - 0 - 1);
    assert (lognot a = (-1) % p);
    assert (sub_mod #n 0 0 = 0);
    assert (lognot a = sub_mod (sub_mod 0 0) 1)
  end

private
val lemma_mod_variation: #n:pos -> a:uint_t n ->
  Lemma (a <> 0 ==> ((-a) % pow2 n) - 1 % pow2 n = (((-a) % pow2 n) - 1) % pow2 n)
let lemma_mod_variation #n a = ()

val lemma_one_mod_pow2: #n:pos -> 
  Lemma (1 = 1 % (pow2 n))
let lemma_one_mod_pow2 #n = ()

#set-options "--z3rlimit 250"
// cwinter: this one is very brittle; it requires hints to pass.
private
val lemma_lognot_value_variation: #n:pos -> a:uint_t n ->
  Lemma (a <> 0 ==> lognot #n a = (-a) % (pow2 n) - 1 % (pow2 n))
let lemma_lognot_value_variation #n a = 
  if a <> 0 then
  begin
    let p = pow2 n in
    lemma_lognot_value_mod a;
    assert (lognot a = p - a - 1);
    assert (lognot a = p + (0 - a) - 1);
    FStar.Math.Lemmas.lemma_mod_sub_1 a p;
    assert ((-a) % p = p - (a%p));
    assert (lognot #n a = p - (a % p) - 1);
    lemma_one_mod_pow2 #n;
    assert (lognot #n a = p - (a % p) - (1 % p));
    assert (p - a - 1 = p - (a % p) - (1 % p));
    assert (- a - 1 = -(a % p) - (1 % p));
    assert (-a = - (a % p));
    assert (-1 = -(1 %p))
  end
#reset-options

val lemma_lognot_value_nonzero: #n:pos -> a:uint_t n ->
  Lemma (a <> 0 ==> (lognot a = sub_mod (sub_mod 0 a) 1))
let lemma_lognot_value_nonzero #n a = 
  if a <> 0 then
  begin
    let p = pow2 n in  
    
    lemma_lognot_value_variation #n a;
    assert (lognot a = (-a) % (pow2 n) - 1 % (pow2 n));
    
    assert (sub_mod (sub_mod 0 a) 1 = (((0 - a) % p) - 1) % p);

    lemma_mod_variation #n a;
    assert (((-a) % p) - 1 % p = (((-a) % p) - 1) % p);
    assert (a <> 0 ==> (-a) % p - 1 % p = (((0 - a) % p) - 1) % p)
  end

val lemma_lognot_value: #n:pos -> a:uint_t n ->
  Lemma (lognot a = sub_mod (sub_mod 0 a) 1)
let lemma_lognot_value #n a = 
  lemma_lognot_value_zero a;
  lemma_lognot_value_nonzero a

val lemma_minus_eq_zero_sub: #n:pos -> a:uint_t n ->
  Lemma (minus #n a = sub_mod #n 0 a)
let lemma_minus_eq_zero_sub #n a =
  let na = lognot a in
  let ma = minus a in
  assert (sub_mod ma 1 = sub_mod (add_mod na 1) 1);
  lemma_sub_add_cancel na 1;
  assert (sub_mod ma 1 = na);
  lemma_lognot_value #n a;
  assert (na = sub_mod (sub_mod 0 a) 1);
  assert (ma = add_mod (sub_mod (sub_mod 0 a) 1) 1);
  lemma_add_sub_cancel (sub_mod 0 a) 1
