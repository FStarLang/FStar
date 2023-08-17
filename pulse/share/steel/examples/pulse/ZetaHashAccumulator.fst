(**
  * This is a port of Zeta.Steel.HashAccumulator to Pulse
  *
  * It models a kind of multiset hash where the the hash value is a cumulative
  * XOR of an underlying hash (from Blake2b) plus a counter that records
  * the number of elements that have been cumualtively hashed so far.
  *
  * It exercises several Pulse features, notably
  *   - Nested records of references and arrays
  *   - Folding & unfolding
  *   - While loops
  *   - Ghost functions
  *   - Use of F* lemmas in Pulse code
  *
  * It is simpler than the Steel version in various ways, as described below.
  *
  * Summarizing:
  *   - The use of erased values is significantly simpler here
  *   - Loops are easier and more structured
  *   - There are fewer rewrites and manipulations of existentials
  *
  * Author: N. Swamy
  *)
module ZetaHashAccumulator
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module A = Pulse.Lib.Array
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
open Pulse.Class.BoundedIntegers
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
#push-options "--fuel 0 --ifuel 0"

(**********************************************************)
(* Pure specification *) 
let u32_to_u64 (x:U32.t) : U64.t = Cast.uint32_to_uint64 x

let bytes = Seq.seq U8.t

inline_for_extraction noextract
let blake2_max_input_length = pow2 32 - 1 - 128

// NOTE: we do not have an agile spec for the keyed hash functionality :(, so
// we're making Blake2-dependent assumptions without corresponding agile predicates
noextract inline_for_extraction
let hashable_bytes = s:bytes { Seq.length s ≤ blake2_max_input_length }

// The hash value is a sequence of 32 bytes
let raw_hash_value_t = Seq.lseq U8.t 32
let e_raw_hash_value_t = l:erased (Seq.seq U8.t) { Seq.length l == 32}

// A hash value is a pair of a (cumulative) hash and a counter
let hash_value_t =
  raw_hash_value_t &
  ℕ

let initial_hash
  : hash_value_t
  = Seq.create 32 0uy, 0

// We just assume a spec for Blake, rather than connecting with the actual HACL code
assume
val blake_spec (d:Seq.seq U8.t { Seq.length d <= blake2_max_input_length})
  : out:Seq.seq U8.t { Seq.length out == 32 }

// Hashing a single value just calls Blake and sets the counter to 1
let hash_one_value (s:Seq.seq U8.t { Seq.length s ≤ blake2_max_input_length })
  : hash_value_t
  = blake_spec s, 1

// Hash accumulation is by XOR
let xor_bytes (s1:bytes) (s2:bytes { Seq.length s1 == Seq.length s2 }) : bytes
  = Seq.init (Seq.length s1)
             (λ i → Seq.index s1 i `FStar.UInt8.logxor` Seq.index s2 i)

// A version (useful for induction) of xor_bytes that only XORs the first i bytes
// In Zeta, i is requires to be less than the length of the s1
// But, here, I "overdefine" the function, which makes it a bit easier to use
// in aggregate_raw_hashes.
// We should also try to make the version with the refinement on i work
let xor_bytes_pfx (s1:bytes)
                  (s2:bytes { Seq.length s1 == Seq.length s2 })
                  (i:ℕ)
: bytes
= let i = if i > Seq.length s1 then Seq.length s1 else i in
  Seq.append
      (xor_bytes (Seq.slice s1 0 i) (Seq.slice s2 0 i))
      (Seq.slice s1 i (Seq.length s1))

// A lemma that says that if we XOR the first i bytes of two sequences, and then
// XOR the i-th byte, we get the same result as XORing the first (i+1) bytes
let extend_hash_value (s1 s2:bytes)
                      (i:ℕ)
  : Lemma (requires Seq.length s1 == Seq.length s2 ∧
                    i < Seq.length s1)
          (ensures  Seq.upd (xor_bytes_pfx s1 s2 i)
                      i
                    (U8.logxor (Seq.index s1 i) (Seq.index s2 i))
                    `Seq.equal`
                    xor_bytes_pfx s1 s2 (i + 1))
  = ()

// Aggregating two hashes is just XORing the two hashes and adding the counters
let aggregate_hashes (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes (fst h0) (fst h1),
    snd h0 + snd h1

(* END Pure Spec *)
(***************************************************************)

(* Model of HACL's blake2b *)
assume
val blake2b:
     nn:SZ.t{1 ≤ SZ.v nn ∧ SZ.v nn ≤ 64}
  -> output: A.array U8.t { A.length output == SZ.v nn}
  -> ll: SZ.t { SZ.v ll <= blake2_max_input_length}
  -> d:A.array U8.t { SZ.v ll ≤ A.length d}
  -> kk: SZ.t { kk == 0sz }                        //We do not use blake2 in keyed mode
  -> _dummy: A.array U8.t // this really should be a NULL, but krml doesn't extract Steel's null pointers yet
  -> #sout:Ghost.erased (Seq.seq U8.t)
  -> #p:perm
  -> #sd:Ghost.erased (Seq.seq U8.t) { Seq.length sd == SZ.v ll}
  -> stt unit
    (A.pts_to output sout ** A.pts_to d #p sd)
    (λ _ → A.pts_to output (blake_spec (Seq.slice sd 0 (SZ.v ll)))
           **
           A.pts_to d #p sd)


// We also don't yet expose a ghost lemma relating the length of a sequence
// to its underlying array. So assuming it here for now.
assume
val array_pts_to_len (#t:Type0) (a:A.array t) (#p:perm) (#x:Seq.seq t)
    : stt_ghost unit emp_inames
          (A.pts_to a #p x)
          (fun _ -> A.pts_to a #p x ** pure (A.length a == Seq.length x))

// Array compare is implemented in other Pulse array modules, but this is not


// yet in a standard place in the library. So, I just assume it here.
```pulse
fn array_compare (#t:eqtype) (l:SZ.t) (a1 a2:A.larray t (SZ.v l))
  requires (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2
  )
  returns res:bool
  ensures (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    (pure (res <==> Seq.equal 's1 's2))
  )
{
  array_pts_to_len a1;
  array_pts_to_len a2;
  Pulse.Lib.Array.compare l a1 a2 
            #p1 #p2
            #(hide #(elseq t l) (reveal 's1))
            #(hide #(elseq t l) (reveal 's2));
}
```

(***************************************************************)
(* Pulse *)

// A buffer with the input to be hashed
let hashable_buffer = b:A.array U8.t { A.length b ≤ blake2_max_input_length }

// A buffer holding the raw hash value
let hash_value_buf  = x:A.array U8.t { A.length x == 32 ∧ A.is_full_array x }

// The main data structure: ha_core
// This contains a buffer with the raw hash value
// and a mutable counter
noeq
type ha_core = {
  acc: hash_value_buf;
  ctr: ref U32.t;
}

// Pulse syntax does not currently allow using record syntax
// So, we define a wrapper for constructing a record
let mk_ha_core acc ctr = { acc; ctr }

// The representation predicate for ha_core ties it to a hash_value_t
// An interesting bit is that at the spec level, a hash_value_t's counter
// is just a nat. But, at the implementation level, it is a U32.t, 
// and the code has to take care of potential overflow. So, at the spec
// level we connect the nat and the concrete counter, indicating that 
// the counter hasn't overflowed yet.
let ha_val_core (core:ha_core) (h:hash_value_t) 
  : vprop
  = A.pts_to core.acc (fst h) **
    exists_ (λ (n:U32.t) →
      pure (U32.v n == snd h) **
      pts_to core.ctr n)

// Working with records and representation predicates involves a bit of boilerplate
// This ghost function packages up permission on the fields of a ha_core into
// ha_val_core using Pulse's primitive `fold` operation
```pulse
ghost
fn fold_ha_val_core (h:ha_core) (#acc:Seq.lseq U8.t 32)
  requires
   A.pts_to h.acc acc **
   pts_to h.ctr n
  ensures
   ha_val_core h (acc, U32.v n)
{
  fold (ha_val_core h (acc, U32.v n));
}
```

// This too is a bit of boilerplate. It use fold_ha_val_core, but also 
// creates and returns a new ha_core value
```pulse
fn package_core (acc:hash_value_buf) (ctr:ref U32.t) 
                (#vacc:erased (Seq.lseq U8.t 32))
  requires A.pts_to acc vacc **
           pts_to ctr 'vctr 
  returns h:ha_core
  ensures ha_val_core h (reveal vacc, U32.v 'vctr) **
          pure (h == mk_ha_core acc ctr)
{
   let core = mk_ha_core acc ctr;
   // It would be nice to have a "rename" primitive
   // So we could write something like
   // rename acc as core.acc, ctr as core.ctr;
   rewrite (A.pts_to acc vacc)
        as  (A.pts_to core.acc vacc);    
   rewrite (pts_to ctr 'vctr)
        as  (pts_to core.ctr 'vctr);
   fold_ha_val_core core;
   core
}
```

// A quirk of the Blake spec is that we need a dummy buffer to pass to it
// which could contain a key, but we're not using it in keyed mode
let dummy_buf = x:A.larray U8.t 1 { A.is_full_array x }

// The full structure holds a core hash value, but also a temporary buffer
// into which to hash new values, and the dummy buffer
noeq
type ha = {
  core: ha_core;
  tmp: hash_value_buf;
  dummy: dummy_buf
}

// Again, we play the same game as with ha_core

let mk_ha core tmp dummy = { core; tmp; dummy }

// A representation predicate for ha, encapsulating an ha_val_core
let ha_val (h:ha) (s:hash_value_t) =
  ha_val_core h.core s **
  exists_ (fun s -> A.pts_to h.tmp s) **
  A.pts_to h.dummy (Seq.create 1 0uy)

// A ghost function to package up a ha_val predicate
// If we were generating this automatically and inserting folds also in the prover,
// then it would be more systematic to replace the first to conjuncts with an ha_val_core
// But, this version is more convenient to use in a manual setting.
```pulse
ghost
fn fold_ha_val (h:ha) (#acc #s:Seq.lseq U8.t 32)
  requires
   A.pts_to h.core.acc acc **
   pts_to h.core.ctr n **
   A.pts_to h.tmp s **
   A.pts_to h.dummy (Seq.create 1 0uy)
  ensures
   ha_val h (acc, U32.v n)
{
    fold_ha_val_core h.core; //fails with ill-typed subst, in case of missing implicit arg
    fold (ha_val h (acc, U32.v n))
}
```

// A function that builds a ha record from its fields
// Again, if we were to do generate this, then the first two conjuncts
// and acc, ctr arguments would be replaced by ha_core/ha_val_core
```pulse
fn package (acc:hash_value_buf) (ctr:ref U32.t) (tmp:hash_value_buf) (dummy:dummy_buf)
           (#vacc:erased (Seq.lseq U8.t 32))
           (#vtmp:erased (Seq.lseq U8.t 32))
  requires A.pts_to acc vacc **
           pts_to ctr 'vctr **
           A.pts_to tmp vtmp **
           A.pts_to dummy (Seq.create 1 0uy)
  returns h:ha
  ensures ha_val h (reveal vacc, U32.v 'vctr) **
          pure (h == mk_ha (mk_ha_core acc ctr) tmp dummy)
{
   let ha = mk_ha (mk_ha_core acc ctr) tmp dummy;
   rewrite (A.pts_to acc vacc)
        as  (A.pts_to ha.core.acc vacc);    
   rewrite (pts_to ctr 'vctr)
        as  (pts_to ha.core.ctr 'vctr);
   rewrite (A.pts_to tmp vtmp)
        as  (A.pts_to ha.tmp vtmp);
   rewrite (A.pts_to dummy (Seq.create 1 0uy))
        as  (A.pts_to ha.dummy (Seq.create 1 0uy));
   fold_ha_val ha;
   ha
}
```

// End boilerplate

// Allocting a new instance of ha
```pulse
fn create (_:unit)
    requires emp
    returns h:ha
    ensures ha_val h initial_hash
{  
    let acc = A.alloc 0uy 32sz;
    let ctr = alloc 0ul;
    let tmp = A.alloc 0uy 32sz;
    let dummy = A.alloc 0uy 1sz;
    package acc ctr tmp dummy
}
```

// Free'ing an ha
```pulse
fn reclaim (s:ha) (#h:hash_value_t) 
    requires ha_val s h
    ensures emp
{
    unfold (ha_val s h);
    unfold (ha_val_core s.core h);
    free s.core.ctr;
    A.free s.core.acc;
    A.free s.tmp;
    A.free s.dummy
}
```



// Aggregating two raw hashes XOR's them byte-by-byte
// Compared to the version in Zeta.Steel, this is significantly cleaner
// That one uses a for loop, but we don't have that yet in Pulse,
// so I use a while instead.
// Aside from that, the invariant can be written in place
// the only explicit proof hints are the ones you would expect,
// i.e., the two asserts to convert Seq.equal to pure equality
// and a call to the extend_hash-value lemma.
//
// Note, I had first tried a vairant of this with a refinement on wi
// in the invariant to constrain its length, but that led to various problems.
// I should try that again and open issues. 
#push-options "--retry 2 --ext 'pulse:rvalues'" // GM: Part of this VC fails on batch mode, not on ide...
```pulse
fn aggregate_raw_hashes (b1 b2: hash_value_buf)
                        (#s1 #s2:e_raw_hash_value_t)
  requires 
    A.pts_to b1 s1 **
    A.pts_to b2 s2
  ensures
    A.pts_to b1 (xor_bytes s1 s2) **
    A.pts_to b2 s2
{
    let mut i = 0sz;
    assert (pure (s1 `Seq.equal` xor_bytes_pfx s1 s2 0));
    while ((i < 32sz))
    invariant b.
        exists wi.
            pts_to i wi **
            A.pts_to b1 (xor_bytes_pfx s1 s2 (v wi)) **
            A.pts_to b2 s2 **
            pure (b == (wi < 32sz))
    {
      let x1 = b1.(i);
      let x2 = b2.(i);
      b1.(i) <- U8.logxor x1 x2;
      extend_hash_value s1 s2 (v i);
      i := i + 1sz;
    };
    assert (pure (xor_bytes_pfx s1 s2 32 `Seq.equal` xor_bytes s1 s2))
}
```
#pop-options

// Aggregates hashes has to handle the case where the ctr overflows
// Again, this is cleaner than the Steel version, has fewer rewrites
// and auxiliary definitions, e.g., using an `if` in the ensures works
// fine here but not in Steel
```pulse
fn aggregate (b1 b2: ha_core)
  requires
    ha_val_core b1 'h1 **
    ha_val_core b2 'h2
  returns ok:bool
  ensures
    ha_val_core b1 (if ok then aggregate_hashes 'h1 'h2 else 'h1) **
    ha_val_core b2 'h2
{
  unfold (ha_val_core b1 'h1);
  unfold (ha_val_core b2 'h2);
  let ctr1 = !b1.ctr;
  let ctr2 = !b2.ctr;
  match (safe_add ctr1 ctr2) {
    Some ctr -> {
      aggregate_raw_hashes b1.acc b2.acc;
      b1.ctr := ctr;
      fold_ha_val_core b1;
      fold_ha_val_core b2;
      true
    }
    None -> {
      fold_ha_val_core b1;
      fold_ha_val_core b2;
      false
    }
  }
}
```

// compare compares the underlying arrays and the counters
```pulse
fn compare (b1 b2:ha)
  requires
    ha_val b1 'h1 **
    ha_val b2 'h2
  returns b:bool
  ensures
    ha_val b1 'h1 **
    ha_val b2 'h2 **
    pure (b <==> ('h1 == 'h2))
{ 
  unfold (ha_val b1 'h1); unfold (ha_val_core b1.core 'h1);
  unfold (ha_val b2 'h2); unfold (ha_val_core b2.core 'h2);
  let ctr1 = !b1.core.ctr;
  let ctr2 = !b2.core.ctr;
  if (ctr1 <> ctr2)
  {
    fold_ha_val b1;
    fold_ha_val b2;
    false
  }
  else
  {
    let res = array_compare 32sz b1.core.acc b2.core.acc;
    fold_ha_val b1;
    fold_ha_val b2;
    res
  }
}
```

// Finally, `add` hashes a new input and accumulates it into the h:ha
// The main work is to break the ha into two ha_cores
//  - one for the underlying ha
//  - and another using the tmp buffer and a local counter for the
//    the hash of the input
// And then aggregate these two ha_cores into the first one
// And then to repackage it as an ha
```pulse
fn add (ha:ha) (input:hashable_buffer) (l:SZ.t)
       (#s:(s:erased bytes {SZ.v l <= Seq.length s /\  SZ.v l <= blake2_max_input_length}))
  requires
    ha_val ha 'h **
    A.pts_to input #p s
  returns ok:bool
  ensures
    ha_val ha (if ok then aggregate_hashes 'h (hash_one_value (Seq.slice s 0 (SZ.v l))) else 'h) **
    A.pts_to input #p s
{ 
   let mut ctr = 1ul;
   unfold (ha_val ha 'h);
   array_pts_to_len input;
   blake2b 32sz ha.tmp l input 0sz ha.dummy;
   let ha' = package_core ha.tmp ctr;
   let v = aggregate ha.core ha';
   with w. unfold (ha_val_core ha' w);
   // would be nice to write this as
   // rename ha'.acc as ha.tmp
   // Or, at least, `with w. rewrite ... `
   // Rather than having to write an assert and then a rewrite
   with w. assert (A.pts_to ha'.acc w);
   rewrite (A.pts_to ha'.acc w)
        as (A.pts_to ha.tmp w); 
   with w. unfold (ha_val_core ha.core w);
   fold_ha_val ha;
   with w. assert (pts_to ha'.ctr w);
   rewrite (pts_to ha'.ctr w)
        as (pts_to ctr w);
   v
}
```
