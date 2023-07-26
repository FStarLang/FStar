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
assume val coerce_op (s:pht_sig) (sz:pos) (repr:repr_t s sz)
    (o:option (s.valt & nat)) (k:s.keyt) (v:s.valt) 
    : (o:(option (s.valt & nat))
      {match o with 
      | Some (v,i) -> i<sz /\ repr @@ i == Used k v
      | None -> true})

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

  unfold (models s pht ht);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true)) 
  invariant b. exists (voff:nat) (vcont:bool). (
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then R.pts_to ret full_perm None
      else R.pts_to ret full_perm (PHT.lookup pht k)) ** 
    pure (
      pht.sz == sz /\
      sz > 0 /\
      voff >= 0 /\ voff <= sz /\
      walk pht.repr cidx k voff == lookup_repr pht.repr k /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = sz) {
      // FIXME: need to set cont to false
      // cont := false;
      // assume_ (R.pts_to ret full_perm (PHT.lookup pht k));
      ()
    } else {
      let idx = (cidx+voff)%sz;
      let c = op_Array_Index ht.contents #full_perm #pht.repr (coerce_us idx);
      match c {
        Used k' v' -> { 
          if (k' = k) {
            cont := false;
            write ret (Some v') #None;
            assert_ (pure (unique_keys s sz pht.spec pht.repr)); // Don't need this assert
            assert_ (pure (lookup_repr_index pht.repr k == Some (v', US.v (coerce_us idx)))); // Need this assert
            ()
          } else {
            off := voff + 1;
            assume_ (pure (lookup_repr pht.repr k == walk pht.repr cidx k (voff+1)));
            ()
          }}
        Clean -> {
          cont := false;
          // FIXME: prove lookup result
          assert_ (pure (pht.repr @@ US.v (coerce_us idx) == Clean));
          assume_ (pure (lookup_repr_index pht.repr k == None)); // FIXME: maybe we need a lemma that says if 
                                                                 // all used not by from cidx to idx and repr @@ idx = Clean
                                                                 // then lookup_repr k = None
          assert_ (R.pts_to ret full_perm (PHT.lookup pht k));
          ()
         }
        Zombie -> {
          off := voff + 1;
          assume_ (pure (lookup_repr pht.repr k == walk pht.repr cidx k (voff+1)));
          ()
         }
      };
    };
  };
  fold (models s pht ht);
  assert_ (R.pts_to ret full_perm (PHT.lookup pht k)); // Need this assert
  let o = !ret;
  o
}
```

// ```pulse
// fn insert (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
//           (ht:ht s) (k:s.keyt) (v:s.valt)
//   requires models s pht ht
//   ensures  models s (PHT.insert pht k v) ht
// {
//   let sz = ht.sz;
//   let a = ht.contents;
//   let cidx = canonical_index k sz;
//   let mut off = coerce_nat 0;
//   let mut cont = true;

//   while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
//   invariant b. exists (voff:nat) (vcont:bool). (
//     R.pts_to off full_perm voff **
//     R.pts_to cont full_perm vcont **
//     `@(if vcont 
//       then models s pht ht
//       else models s (PHT.insert pht k v) ht) **
//     pure (
//       voff >= 0 /\ voff <= sz /\
//       b == (voff <= sz && vcont = true)
//     ))
//   {
//     let voff = !off;
//     if (voff=sz) {
//       ()
//     } else {
//       unfold (models s pht ht);
//       let idx = coerce_us ((cidx+voff)%sz);
//       let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
//       match c {
//         Used k' v' -> { 
//           if (k' = k) {
//             op_Array_Assignment ht.contents idx (mk_used_cell k v);
//             cont := false;
//             // FIXME: prove seq upd
//             assume_ (pure ((PHT.insert pht k v).repr `Seq.equal` 
//               Seq.upd pht.repr (US.v idx) (mk_used_cell k v))); 
//             fold (models s (PHT.insert pht k v) ht);
//             ()
//           } else {
//             off := voff + 1;
//             fold (models s pht ht);
//             ()
//           } 
//         }
//         Clean -> {
//           op_Array_Assignment ht.contents idx (mk_used_cell k v);
//           cont := false;
//           // FIXME: prove seq upd
//           assume_ (pure ((PHT.insert pht k v).repr `Seq.equal` 
//             Seq.upd pht.repr (US.v idx) (mk_used_cell k v)));
//           fold (models s (PHT.insert pht k v) ht);
//           ()
//         }
//         Zombie -> {
//           fold (models s pht ht);
//           let o = lookup_repr_index #s #sz pht.repr k; // FIXME: Pulse impl of lookup_index
//           unfold (models s pht ht);
//           match o {
//             Some p -> {
//               op_Array_Assignment ht.contents (coerce_us (snd p)) Zombie;
//               op_Array_Assignment ht.contents idx (mk_used_cell k v);
//               cont := false;
//               // FIXME: prove seq upd
//               assume_ (pure ((PHT.insert pht k v).repr `Seq.equal` 
//                 Seq.upd (Seq.upd pht.repr (US.v (coerce_us (snd p))) Zombie) (US.v idx) (mk_used_cell k v)));
//               fold (models s (PHT.insert pht k v) ht);
//               ()
//             }
//             None -> { 
//               op_Array_Assignment ht.contents idx (mk_used_cell k v); 
//               cont := false;
//               // FIXME: prove seq upd
//               assume_ (pure ((PHT.insert pht k v).repr `Seq.equal` Seq.upd pht.repr (US.v idx) (mk_used_cell k v)));
//               fold (models s (PHT.insert pht k v) ht);
//               ()
//             }
//           };
//         }
//       };
//     };
//   }
// }
// ```

// ```pulse
// fn delete (#s:pht_sig) (#pht:pht s) 
//           (ht:ht s) (k:s.keyt)
//   requires models s pht ht
//   ensures  models s (PHT.delete pht k) ht
// {
//   let sz = ht.sz;
//   let a = ht.contents;
//   let cidx = canonical_index k sz;
//   let mut off = coerce_nat 0;
//   let mut cont = true;

//   while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
//   invariant b. exists (voff:nat) (vcont:bool). (
//     R.pts_to off full_perm voff **
//     R.pts_to cont full_perm vcont **
//     `@(if vcont 
//       then models s pht ht
//       else models s (PHT.delete pht k) ht) **
//     pure (
//       voff >= 0 /\ voff <= sz /\
//       b == (voff <= sz && vcont = true)
//     ))
//   {
//     let voff = !off;
//     if (voff=sz) {
//       ()
//     } else {
//       unfold (models s pht ht);
//       let idx = (cidx+voff)%sz;
//       let c = op_Array_Index ht.contents #full_perm #pht.repr (coerce_us idx);
//       match c {
//         Used k' v' -> { 
//           if (k' = k) {
//             op_Array_Assignment ht.contents (coerce_us idx) Zombie;
//             cont := false;
//             // FIXME: prove seq upd
//             assert_ (pure (pht.repr @@ US.v (coerce_us idx) == Used k v'));
//             assume_ (pure (Seq.upd pht.repr (US.v (coerce_us idx)) Zombie `Seq.equal` (PHT.delete pht k).repr));
//             fold (models s (PHT.delete pht k) ht);
//             ()
//           } else {
//             off := voff + 1;
//             fold (models s pht ht);
//             ()
//           } 
//         }
//         Clean -> {
//           cont := false;
//           // FIXME: prove equality
//           assume_ (pure (pht == (PHT.delete pht k)));
//           fold (models s (PHT.delete pht k) ht);
//           ()
//         }
//         Zombie -> { 
//           off := voff + 1;
//           fold (models s pht ht);
//           () 
//         }
//       };
//     };
//   }
// }
// ```