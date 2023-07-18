module PulseHashTable
module PM = Pulse.Main
open Steel.ST.Array
open Steel.FractionalPermission
open Steel.ST.Util
open FStar.Ghost
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module LK = Steel.ST.SpinLock
module PHT = LinearScanHashTable
open LinearScanHashTable

noeq
type ht (s : pht_sig) = {
  sz : pos;
  contents : A.larray (cell s.keyt s.valt) sz;
}

let models (s:pht_sig) (pht:pht s) (ht:ht s) : vprop
= A.pts_to ht.contents full_perm pht.repr `star`
  pure (pht.sz == ht.sz)

let coerce_nat (n:int{n>=0}) : nat = n
let coerce_us (n:nat) : US.t = assume (US.fits n); US.uint_to_t n
let refine_repr (s:pht_sig) (sz:pos) (i:US.t) (repr:Seq.lseq (cell s.keyt s.valt) sz) 
  : s:(Seq.lseq (cell s.keyt s.valt) sz){US.v i < sz} = admit()
  // : stt (s:(Seq.lseq (cell s.keyt s.valt) sz){US.v i < sz})
  //       (requires pure (US.v i < sz))
  //       (ensures fun _ -> emp)
  // = fun _ -> repr

(* 
  See FIXME comments for current debugging status
*)
#set-options "--split_queries no"
// [@@expect_failure]
```pulse
fn insert (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
          (ht:ht s) (k:s.keyt) (v:s.valt)
  requires models s pht ht
  ensures  models s (PHT.insert pht k v) ht
{
  unfold (models s pht ht);
  let sz = ht.sz;
  let a = ht.contents;
  let cidx = canonical_index k sz;
  let mut off = coerce_nat 0;
  let mut cont = true;
  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. exists (voff:nat) (vcont:bool) (s:Seq.lseq (cell s.keyt s.valt) pht.sz). (
    A.pts_to ht.contents full_perm s `star`
    // `@(if vcont=true 
    //   then (A.pts_to ht.contents full_perm pht.repr) 
    //   else (A.pts_to ht.contents full_perm (PHT.insert pht k v).repr)) `star`
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    pure (
      pht.sz == ht.sz /\
      voff >= 0 /\ voff <= sz /\
      // walk_ pht.repr cidx k off == PHT.insert pht k v /\
      // walk pht.repr cidx k off == lookup_repr pht.repr k /\
      // strong_all_used_not_by #s #sz pht.repr cidx voff k /\
      (if vcont=true
        then s == pht.repr
        else s == (PHT.insert pht k v).repr) /\
      b == (voff <= sz && vcont = true)
    )
  )
  {
    // if (off=sz) {
    // admit()
    // } else {
    let voff = !off;
    let idx = coerce_us ((cidx+voff)%sz);
    assume_ (pure (US.v idx < pht.sz)); // FIXME: can prove based on modulo calc above
    let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
    match c {
      Used k' v' -> { 
        if (k' = k) {
          op_Array_Assignment ht.contents idx (mk_used_cell k v);
          cont := false;
          ()
        } else {
          off := voff + 1;
          ()
        } 
      }
      Clean -> {
        op_Array_Assignment ht.contents idx (mk_used_cell k v);
        cont := false;
        ()
      }
      Zombie -> {
        let o = lookup ht k;
        match o {
          Some p -> {
            op_Array_Assignment ht.contents (snd p) Zombie;
            op_Array_Assignment ht.contents idx (mk_used_cell k v);
          }
          None -> { op_Array_Assignment ht.contents idx (mk_used_cell k v); }
        };
        cont := false;
        ()
      }
    };};
    fold (models s (PHT.insert pht k v) ht);
    ()
}
```

(* 
  Basic implementation of delete expected to fail, working out the kinks 
  should follow easily after I get insert working
*)
[@@expect_failure]
```pulse
fn delete (#s:pht_sig) (#pht:pht s) 
          (ht:ht s) (k:s.keyt)
  requires models s pht ht
  ensures  models s (PHT.delete pht k) ht
{
  let sz = ht.sz;
  let a = ht.contents;
  let cidx = canonical_index k sz;
  let mut off = 0;
  while (let voff = !off; (voff <= sz)) (* include the case voff=sz *)
  invariant b. exists (voff:nat). (
    R.pts_to off full_perm voff **
    pure (
      voff >= 0 /\ voff <= sz /\
      // walk pht.repr cidx k off == lookup_repr pht.repr k /\
      // strong_all_used_not_by #s #sz pht.repr cidx voff k /\
      b == (voff <= sz)
    )
  )
  {
    let voff = !off;
    if (voff = sz) {
    return () (* element is not in the table *)
    } else {
    let idx = (cidx+voff)%sz;
    let c = A.index ht.contents idx;
    match c {
      Used k' v' -> { if (k' = k) {
        op_Array_Assignment ht.contents idx Zombie;
        return ()
      }}
      Clean -> { return () (* element is not in the table *) }
      Zombie -> { noop() }
    };
    off := voff - 1;
    ()
  }}
}
```

```pulse
fn lookup (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
          (ht:ht s) (k:s.keyt)
  requires models s pht ht
  returns  o:(o:option s.valt{o == PHT.lookup pht k})
  ensures  models s pht ht
{
  admit()
}
```