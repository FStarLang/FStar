module StringMatching
open FStar.Seq
open FStar.Mul
#set-options " --ext context_pruning_no_ambients"
(* Some basic notions *)

// Type of a string of t
let str (t:eqtype) = FStar.Seq.seq t

// w is a prefix of x
let is_prefix #t (w x:str t) 
: prop
= let wlen = length w in
  let xlen = length x in
  wlen <= xlen /\
  Seq.slice x 0 wlen == w

// w is a suffix of x
let is_suffix #t (w x:str t)
: prop
= let wlen = length w in
  let xlen = length x in
  wlen <= xlen /\
  Seq.slice x (xlen - wlen) xlen == w

// property of overlapping suffixes
let overlapping_suffix #t (x y z:str t)
: Lemma
  (requires
    x `is_suffix` z /\
    y `is_suffix` z /\
    length x >= length y)
  (ensures
    y `is_suffix` x /\
    (length x == length y ==> x == y))
= ()

// x occurs at position i in y
let occurs_at #t (i:nat) (x y:str t)
: prop
= i + Seq.length x <= Seq.length y /\
  x `Seq.equal` Seq.slice y i (i + Seq.length x)

// a utility to search an integer range
let rec find_in_range
    (i:nat) (j:nat {i <= j}) 
    (body: (c:nat { i <= c /\ c <= j} -> bool))
: Tot 
 (o:option nat {
   match o with
   | None -> (forall c. i <= c /\ c <= j ==> not (body c))
   | Some i' -> 
      i <= i' /\ i' <= j /\ body i' /\
      (forall c. i <= c /\ c < i' ==> not (body c))
  }) (decreases j - i)
= if body i then Some i
  else if i = j then None
  else find_in_range (i+1) j body

// fine the first occurrence of pattern in x
// if it exists, otherwise return None
// naively scans x at each index trying to match pattern
let naive_string_matcher #t (x pattern:str t)
: o:option nat {
  match o with
  | None -> forall j. ~(pattern `occurs_at j` x)
  | Some i -> pattern `occurs_at i` x
}
= let n = length x in
  let m = length pattern in
  if n < m then None
  else find_in_range 0 (n - m) (fun i -> pattern = Seq.slice x i (i + m))

// Rabin-Karp matcher
// The idea is to compute a "rolling hash" of the string
// and to compare the hash of the pattern with the hash of
// the substring of the string
// If the hashes are equal, we check the equality of the
// substrings. If not the hashes are different and so 
// the substrings are different, and we can continue


// The hash function is a polynomial hash function
// h(x) = (x[0] * b^(m-1) + x[1] * b^(m-2) + ... + x[m-1] * b^0) % p
let rec hash 
    (x:str nat) (base:nat) (prime:nat{prime <> 0}) 
    (i:nat) (j:nat { i <= j /\ j <= Seq.length x })
: nat
= if i = j then 0
  else (
    let lsd = Seq.index x (j - 1) in 
    let h = hash x base prime i (j - 1) in
    (base * h + lsd) % prime
  )

// A lot of the proof is about proving properties about the hash function
let rec pow (base m:nat) : nat =
  if m = 0 then 1
  else pow base (m - 1) * base

// The hash function is already reduced modulo prime.
// Reducing it again does not change the value
let hash_mod_idem (x:str nat) (base:nat) (prime:nat{prime <> 0}) 
    (i:nat) (j:nat { i <= j /\ j <= Seq.length x })
: Lemma 
  (hash x base prime i j == hash x base prime i j % prime)
= if i = j then ()
  else (
    let lsd = Seq.index x (j - 1) in
    let h = hash x base prime i (j - 1) in
    FStar.Math.Lemmas.lemma_mod_twice (base * h + lsd) prime
  )   

// A trivial helper
let pow_lemma (base m:nat) : Lemma (base * pow base m == pow base (m + 1)) = ()

// Reasoning about modulo is painful, and needs lots of explicit lemmas
// from FStar.Math.Lemmas
let lemma_mod_add_distr_l (a:int) (b:int) (n:pos) : Lemma ((a%n + b) % n = (a + b) % n) =
  FStar.Math.Lemmas.lemma_mod_add_distr b a n

let lemma_mod_add_3 (a b c:int) (p:pos)
: Lemma (((a + b)%p + c)%p == ((a + c)%p + b)%p)
= lemma_mod_add_distr_l (a + b) c p;
  lemma_mod_add_distr_l (a + c) b p

#push-options "--z3rlimit_factor 10 --ifuel 0 --fuel 2 --split_queries no"
#restart-solver
// This is the main utility lemma on the hash function
// It allows inverting the hash to inspect the most significant digit
let rec hash_inversion
    (x:str nat) (base:nat) (prime:nat{prime <> 0}) 
    (i:nat) (j:nat { i < j /\ j <= Seq.length x })
: Lemma
  (ensures hash x base prime i j ==
           (hash x base prime (i + 1) j + 
            pow base (j - i - 1) * Seq.index x i) % prime)
  (decreases j - i)
= if j = i + 1 then ()
  else (
    let lsd = Seq.index x (j - 1) in
    let h = hash x base prime i (j - 1) in
    hash_inversion x base prime i (j - 1);
    let h_lsd = base * hash x base prime (i + 1) (j - 1) in
    let msd = pow base (j - i - 1) * Seq.index x i in
    FStar.Pure.BreakVC.break_vc();
    let aux () 
    : Lemma (base * h % prime == (h_lsd + msd) % prime)
    = calc(==) {
          base * h % prime;
        (==) { hash_inversion x base prime i (j - 1) }
          (base * ((hash x base prime (i + 1) (j - 1) + 
                    pow base (j - i - 2) * Seq.index x i)%prime)) % prime;
        (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r 
                  base 
                  (hash x base prime (i + 1) (j - 1) + 
                    pow base (j - i - 2) * Seq.index x i)
                  prime }
        (base * (hash x base prime (i + 1) (j - 1) + 
                  pow base (j - i - 2) * Seq.index x i)) % prime;
        (==) { 
          FStar.Math.Lemmas.distributivity_add_right
                   base
                   (hash x base prime (i + 1) (j - 1))
                   (pow base (j - i - 2) * Seq.index x i);
                pow_lemma base (j - i - 2) }
          (h_lsd + msd) % prime;            
      }
    in
    calc (==) {
      hash x base prime i j;
    (==) {}
      (base * h + lsd) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l
              (base * h) lsd prime }
      (base * h % prime + lsd) % prime;
    (==) { aux () }
    ((h_lsd + msd) % prime + lsd) % prime;
    (==) { lemma_mod_add_3 h_lsd msd lsd prime }
    ((h_lsd + lsd)%prime + msd)%prime;
    }
  )
#pop-options

// The rolling hash computes the hash of the next substring
// by removing the most significant digit and adding the least
// significant digit

// remove_msd removes the most significant digit
// from the hash of the substring x[i..j] and returns the
// hash of the substring x[i+1..j]
let remove_msd 
     (x:str nat) 
     (base:nat)
     (prime:nat {prime <> 0})
     (i:nat) 
     (j:nat { i < j /\ j < Seq.length x })
     (h:nat)
     (pow_base_m: nat { pow_base_m == pow base (j - i - 1) })
: nat
= let msd = Seq.index x i in
  (h - msd * pow_base_m) % prime

// Another helper lemma about modulo
let lemma_mod_add_sub_cancel (a b:int) (p:pos)
: Lemma (((a + b)%p - b)%p == a%p)
= calc (==) {
    ((a + b)%p - b)%p;
  (==) {}
    ((-b) + (a + b)%p)%p;
  (==) { FStar.Math.Lemmas.lemma_mod_add_distr (-b) (a + b) p }
    a % p;
  }

// remove_msd is correct
let remove_msd_lemma
     (x:str nat) 
     (base:nat)
     (prime:nat {prime <> 0})
     (i:nat) 
     (j:nat { i < j /\ j < Seq.length x })
     (h:nat { h == hash x base prime i j })
     (pow_base_m: nat { pow_base_m == pow base (j - i - 1) })
: Lemma
  (ensures remove_msd x base prime i j h pow_base_m == hash x base prime (i + 1) j)
= let msd = Seq.index x i in
  calc (==) {
    remove_msd x base prime i j h pow_base_m;
  (==) {}
    (h - msd * pow_base_m) % prime;
  (==) { hash_inversion x base prime i j }
    ((hash x base prime (i + 1) j + msd * pow_base_m) % prime - msd * pow_base_m) % prime;
  (==) { lemma_mod_add_sub_cancel (hash x base prime (i + 1) j) (msd * pow_base_m) prime }
    (hash x base prime (i + 1) j)%prime;
  (==) { hash_mod_idem x base prime (i + 1) j }
    hash x base prime (i + 1) j;
  }

// Adding the least-significant digit
// to the hash of the substring x[i..j] returns the
// hash of the substring x[i..j+1]
let add_lsd 
     (x:str nat) 
     (base:nat)
     (prime:nat {prime <> 0})
     (i:nat) 
     (j:nat { i <= j /\ j < Seq.length x })
     (h:nat)
     (pow_base_m: nat { pow_base_m == pow base (j - i) })
: nat
= let lsd = Seq.index x j in
  (base * h + lsd) % prime

// add_lsd is correct
let add_lsd_lemma
     (x:str nat) 
     (base:nat)
     (prime:nat {prime <> 0})
     (i:nat) 
     (j:nat { i <= j /\ j < Seq.length x })
     (h:nat { h == hash x base prime i j })
     (pow_base_m: nat { pow_base_m == pow base (j - i) })
: Lemma
  (ensures add_lsd x base prime i j h pow_base_m == hash x base prime i (j + 1))
  (decreases j - i)
= ()

// The rolling hash computes the hash of the next substring
// by removing the most significant digit and adding the least
// significant digit.
// It could be done more efficiently by doing only one modulo
// in the end, rather than two
let rolling_hash 
     (x:str nat) 
     (base:nat)
     (prime:nat {prime <> 0})
     (i:nat) 
     (j:nat { i < j /\ j < Seq.length x })
     (h:nat { h == hash x base prime i j })
     (pow_base_m: nat { pow_base_m == pow base (j - i - 1) })
: h:nat { h == hash x base prime (i + 1) (j + 1) }
= let h0 = remove_msd x base prime i j h pow_base_m in
  remove_msd_lemma x base prime i j h pow_base_m;
  assert (h0 == hash x base prime (i + 1) j);
  let res = add_lsd x base prime (i + 1) j h0 pow_base_m in
  add_lsd_lemma x base prime (i + 1) j h0 pow_base_m;
  res

// Now for some lemmas about hashes on slices of a string

// x[i..j] == y[i'..j'] means that the two slices are equal
let eq_sub_seq #a (x:seq a) (i j:nat) (y:seq a) (i' j':nat)
: prop
= j - i == j' - i' /\
  j <= Seq.length x /\
  j' <= Seq.length y /\
  (forall (k:nat). k < j - i ==> Seq.index x (i + k) == Seq.index y (i' + k))

let rec hash_slice_lemma
      (x y:str nat) 
      (base:nat)
      (prime:nat {prime <> 0})
      (i:nat) 
      (j:nat { i <= j /\ j <= Seq.length x })
      (i':nat)
      (j':nat { i' <= j' /\ j' <= Seq.length y})
: Lemma
  (requires eq_sub_seq x i j y i' j')
  (ensures hash x base prime i j == hash y base prime i' j')
  (decreases j - i)
= if i = j then ()
  else hash_slice_lemma x y base prime i (j - 1) i' (j' - 1)

// A helper predicate to state our main correctness property
let maybe_found #t (xs pat:str t) (o:option nat) =
  match o with
  | None -> forall j. ~(pat `occurs_at j` xs)
  | Some i -> pat`occurs_at i` xs

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4 --split_queries no"
#restart-solver
let rabin_karp_matcher_nat
    (xs pat:str nat)
    (base:nat)
    (prime:nat{prime <> 0})
: o:option nat { maybe_found xs pat o } // the same spec as our naive matcher
= let m = length pat in
  let n = length xs in
  if n < m then None
  else if m = 0 then Some 0
  else (
    let pow_base_m = pow base (m - 1) in
    let hpat = hash pat base prime 0 m in
    let xpat = hash xs base prime 0 m in
    let rec loop 
          (i:nat { 0 <= i /\ i <= n - m /\ (forall k. k < i ==> ~(pat `occurs_at k` xs)) })
          (xpat:nat { xpat == hash xs base prime i (i + m) })
    : Tot (o:option nat { maybe_found xs pat o }) (decreases (n - m - i))
    = let found =
        if xpat = hpat
        then pat = Seq.slice xs i (i + m)
        else (
          hash_slice_lemma xs (Seq.slice xs i (i + m)) base prime i (i + m) 0 m;
          false
        )
      in
      if found then Some i 
      else if i = n - m then None
      else let xnext = rolling_hash xs base prime i (i + m) xpat pow_base_m in
           loop (i + 1) xnext
    in
    loop 0 xpat
  )
#pop-options

// One-level of indirection:
// Rather than on strings of nat, we can work on strings of t
// so long as we have some map from nat -> t
// Of course, the hash works best if the as_digit map is injective


//Re-exporting some functions from the library with patterns to make
//our proofs a bit easier
let map_seq_len #a #b f s
: Lemma 
  (ensures Seq.length (map_seq f s) == Seq.length s)
  [SMTPat (Seq.length (map_seq f s))]
= FStar.Seq.map_seq_len #a #b f s

let map_seq_index #a #b f s i
: Lemma 
  (ensures (Seq.index (map_seq f s) i == f (Seq.index s i)))
  [SMTPat (Seq.index (map_seq f s) i)]
= FStar.Seq.map_seq_index #a #b f s i

let rec slice_map
    (#t #s:Type)
    (t_xs:Seq.seq t)
    (as_digit: t -> s)
    (i:nat)
    (j:nat { i <= j /\ j <= length t_xs })
: Lemma 
  (ensures Seq.slice (map_seq as_digit t_xs) i j == map_seq as_digit (Seq.slice t_xs i j))
  (decreases j - i)
  [SMTPat (Seq.slice (map_seq as_digit t_xs) i j)]
= if j <> i then slice_map t_xs as_digit i (j - 1);
  assert (
    Seq.slice (map_seq as_digit t_xs) i j `Seq.equal` map_seq as_digit (Seq.slice t_xs i j)
  ) 
   
#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4"
// The main matcher, same as the one on nats, but not with a strings of t
let rabin_karp_matcher
    (#t:eqtype)
    (t_xs t_pat:str t)
    (as_digit: t -> nat)
    (base:nat)
    (prime:nat{prime <> 0})
: o:option nat { maybe_found t_xs t_pat o }
= let m = length t_pat in
  let n = length t_xs in
  if n < m then None
  else if m = 0 then Some 0
  else (
    let pow_base_m = pow base (m - 1) in
    let pat = Seq.map_seq as_digit t_pat in
    let xs = Seq.map_seq as_digit t_xs in
    let hpat = hash pat base prime 0 m in
    let xpat = hash xs base prime 0 m in
    let rec loop 
          (i:nat { 0 <= i /\ i <= n - m /\ (forall k. k < i ==> ~(t_pat `occurs_at k` t_xs)) })
          (xpat:nat { xpat == hash xs base prime i (i + m) })
    : Tot (o:option nat { maybe_found t_xs t_pat o }) (decreases (n - m - i))
    = let found =
        if xpat = hpat
        then t_pat = Seq.slice t_xs i (i + m)
        else (
          hash_slice_lemma xs (Seq.slice xs i (i + m)) base prime i (i + m) 0 m;
          false
        )
      in
      if found then Some i 
      else (
        if i = n - m then None
        else let xnext = rolling_hash xs base prime i (i + m) xpat pow_base_m in    
              loop (i + 1) xnext
      )
    in
    loop 0 xpat
  )
#pop-options