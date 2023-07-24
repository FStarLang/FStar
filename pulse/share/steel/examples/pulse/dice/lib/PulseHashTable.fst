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

// [@@expect_failure]
```pulse
fn lookup (#s:pht_sig) (#pht:(p:pht s{not_full p.repr}))  
          (ht:ht s) (k:s.keyt)
  requires models s pht ht
  returns  o:(o:option s.valt{o == PHT.lookup pht k})
  ensures  models s pht ht
{
  let sz = ht.sz;
  let cidx = canonical_index k sz;
  let mut off = coerce_nat 0;
  let mut cont = true;
  let mut ret = None #(s.valt);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true)) 
  invariant b. exists (voff:nat) (vcont:bool). (
    models s pht ht **
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then R.pts_to ret full_perm None
      else R.pts_to ret full_perm (PHT.lookup pht k)) **    
    pure (
      voff >= 0 /\ voff <= sz /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = sz) {
      ()
    } else {
      unfold (models s pht ht);
      let idx = coerce_us ((cidx+voff)%sz);
      let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            cont := false;
            write ret (Some v') #None;
            admit()
          } else {
            off := voff + 1;
            admit() 
          }}
        Clean -> { 
          cont := false;
          admit()
         }
        Zombie -> { 
          off := voff + 1;
          admit() 
         }
      };
    };
  };
  assert_ (R.pts_to ret full_perm (PHT.lookup pht k)); // need this assert
  let o = !ret;
  o
}
```

[@@expect_failure]
```pulse
fn insert (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
          (ht:ht s) (k:s.keyt) (v:s.valt)
  requires models s pht ht
  ensures  models s (PHT.insert pht k v) ht
{
  let sz = ht.sz;
  let a = ht.contents;
  let cidx = canonical_index k sz;
  let mut off = coerce_nat 0;
  let mut cont = true;

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. exists (voff:nat) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then models s pht ht
      else models s (PHT.insert pht k v) ht) **
    pure (
      voff >= 0 /\ voff <= sz /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff=sz) {
      ()
    } else {
      unfold (models s pht ht);
      let idx = coerce_us ((cidx+voff)%sz);
      let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment ht.contents idx (mk_used_cell k v);
            cont := false;
            admit()
          } else {
            off := voff + 1;
            admit()
          } 
        }
        Clean -> {
          op_Array_Assignment ht.contents idx (mk_used_cell k v);
          cont := false;
          admit()
        }
        Zombie -> {
          fold (models s pht ht);
          let o = lookup_repr_index #s #sz pht.repr k; // FIXME: Pulse impl of lookup_index
          unfold (models s pht ht);
          match o {
            Some p -> {
              op_Array_Assignment ht.contents (coerce_us (snd p)) Zombie;
              op_Array_Assignment ht.contents idx (mk_used_cell k v);
              cont := false;
              admit()
            }
            None -> { 
              op_Array_Assignment ht.contents idx (mk_used_cell k v); 
              cont := false;
              admit()
            }
          };
        }
      };
    };
  }
}
```

```pulse
fn delete (#s:pht_sig) (#pht:pht s) 
          (ht:ht s) (k:s.keyt)
  requires models s pht ht
  ensures  models s (PHT.delete pht k) ht
{
  let sz = ht.sz;
  let a = ht.contents;
  let cidx = canonical_index k sz;
  let mut off = coerce_nat 0;
  let mut cont = true;

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. exists (voff:nat) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then models s pht ht
      else models s (PHT.delete pht k) ht) **
    pure (
      voff >= 0 /\ voff <= sz /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff=sz) {
      ()
    } else {
      admit()
      // let idx = coerce_us ((cidx+voff)%sz);
      // assume_ (pure (US.v idx < pht.sz)); // FIXME: can prove based on modulo calc above
      // let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
      // match c {
      //   Used k' v' -> { 
      //     if (k' = k) {
      //       op_Array_Assignment ht.contents idx Zombie;
      //       cont := false;
      //       ()
      //     } else {
      //       off := voff + 1;
      //       ()
      //     } 
      //   }
      //   Clean -> {
      //     cont := false;
      //     ()
      //   }
      //   Zombie -> { 
      //     off := voff + 1;
      //     () 
      //   }
      // };
    };
  }
}
```