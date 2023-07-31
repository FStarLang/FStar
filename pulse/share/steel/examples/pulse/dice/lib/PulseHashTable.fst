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
open Pulse.Class.BoundedIntegers

type bound_us = n:US.t{US.fits (US.v n)}
type pos_us = n:bound_us{US.v n > 0}

noeq
type ht (s : pht_sig) = {
  sz : pos_us;
  contents : A.larray (cell s.keyt s.valt) (US.v sz);
}

let canonical_index_us #s (k : s.keyt) (sz : pos_us) 
  : n:US.t{US.v n == PHT.canonical_index k (US.v sz)} 
  = US.uint_to_t (s.hashf k % US.v sz)

let modulo_us (m:pos_us) (v1 v2:US.t)
  : n:US.t{n<m}
  = US.uint_to_t ((US.v v1 + US.v v2) % US.v m)

let models (s:pht_sig) (ht:ht s) (pht:pht s) : vprop
= A.pts_to ht.contents full_perm pht.repr `star`
  pure (pht.sz == US.v ht.sz)

```pulse
fn pulse_lookup_index (#s:pht_sig) (#pht:(p:pht s{not_full p.repr}))  
                (ht:ht s) (k:s.keyt)
  requires models s ht pht
  returns  o:(o:option (s.valt & bound_us){o == PHT.lookup_index_us pht k})
  ensures  models s ht pht
{
  let sz = ht.sz;
  let cidx = canonical_index_us k sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut ret = None #(s.valt & bound_us);

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true)) 
  invariant b. exists (voff:US.t) (vcont:bool). (
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then R.pts_to ret full_perm None
      else R.pts_to ret full_perm (PHT.lookup_index_us pht k)) ** 
    pure (
      voff <= sz /\
      walk_get_idx pht.repr (US.v cidx) k (US.v voff) == lookup_repr_index pht.repr k /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = sz) {
      cont := false;
      assert_ (R.pts_to ret full_perm None);
      assert_ (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) == None));
    } else {
      let idx = modulo_us sz cidx voff;
      let c = op_Array_Index_nat ht.contents #full_perm #pht.repr (US.v idx);
      match c {
        Used k' v' -> {
          if (k' = k) {
            cont := false;
            write ret (Some (v',idx)) #None;
            assert_ (pure (pht.repr @@ US.v idx == Used k' v'));
            assert_ (pure (lookup_repr_index pht.repr k == Some (v', US.v idx)));
          } else {
            off := voff + 1sz;
            assert_ (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) == walk_get_idx pht.repr (US.v cidx) k (US.v (voff+1sz))));
          }}
        Clean -> {
          cont := false;
          assert_ (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) == None));
          assert_ (R.pts_to ret full_perm (PHT.lookup_index_us pht k));
         }
        Zombie -> {
          off := voff + 1sz;
          assert_ (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) == walk_get_idx pht.repr (US.v cidx) k (US.v (voff+1sz))));
         }
      };
    };
  };
  fold (models s ht pht);
  assert_ (R.pts_to ret full_perm (PHT.lookup_index_us pht k));
  let o = !ret;
  o
}
```

```pulse
fn lookup (#s:pht_sig) (#pht:(p:pht s{not_full p.repr}))  
          (ht:ht s) (k:s.keyt)
  requires models s ht pht
  returns  o:(o:option s.valt{o == PHT.lookup pht k})
  ensures  models s ht pht
{
  let o = pulse_lookup_index #s #pht ht k;
  match o {
    Some p -> { Some (fst p) }
    None -> { None #s.valt }
  }
}
```

```pulse
fn insert (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
          (ht:ht s) (k:s.keyt) (v:s.valt)
  requires models s ht pht
  ensures  models s ht (PHT.insert pht k v)
{
  let sz = ht.sz;
  let cidx = canonical_index_us k sz;
  let mut off = 0sz;
  let mut cont = true;

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true)) 
  invariant b. exists (voff:US.t) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then A.pts_to ht.contents full_perm pht.repr
      else A.pts_to ht.contents full_perm (PHT.insert pht k v).repr) **
    pure (
      voff <= sz /\
      strong_all_used_not_by pht.repr (US.v cidx) (US.v voff) k /\
      walk pht.repr (US.v cidx) k (US.v voff) == lookup_repr pht.repr k /\
      insert_repr_walk #s #pht.sz #pht.spec pht.repr k v (US.v voff) (US.v cidx) () () == insert_repr #s #pht.sz #pht.spec pht.repr k v /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = sz) {
      cont := false;
      assert_ (A.pts_to ht.contents full_perm pht.repr);
    } else {
      let idx = modulo_us sz cidx voff;
      let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment ht.contents idx (mk_used_cell k v);
            cont := false;
            assert_ (pure (insert_repr #s #pht.sz #pht.spec pht.repr k v `Seq.equal` 
              Seq.upd pht.repr (US.v idx) (mk_used_cell k v))); 
          } else {
            off := voff + 1sz;
          } 
        }
        Clean -> {
          op_Array_Assignment ht.contents idx (mk_used_cell k v);
          cont := false;
          assert_ (pure (insert_repr #s #pht.sz #pht.spec pht.repr k v `Seq.equal` 
            Seq.upd pht.repr (US.v idx) (mk_used_cell k v)));
        }
        Zombie -> {
          fold (models s ht pht);
          let o = pulse_lookup_index #s #pht ht k;
          unfold (models s ht pht);
          match o {
            Some p -> {
              op_Array_Assignment ht.contents (snd p) Zombie;
              op_Array_Assignment ht.contents idx (mk_used_cell k v);
              cont := false;
              assert_ (pure (insert_repr #s #pht.sz #pht.spec pht.repr k v `Seq.equal` 
                Seq.upd (Seq.upd pht.repr (US.v (snd p)) Zombie) (US.v idx) (mk_used_cell k v)));
            }
            None -> { 
              op_Array_Assignment ht.contents idx (mk_used_cell k v); 
              cont := false;
              assert_ (pure (insert_repr #s #pht.sz #pht.spec pht.repr k v `Seq.equal` Seq.upd pht.repr (US.v idx) (mk_used_cell k v)));
            }
          };
        }
      };
    };
  };
  fold (models s ht (PHT.insert pht k v));
}
```

```pulse
fn delete (#s:pht_sig) (#pht:pht s) 
          (ht:ht s) (k:s.keyt)
  requires models s ht pht
  ensures  models s ht (PHT.delete pht k)
{
  let sz = ht.sz;
  let cidx = canonical_index_us k sz;
  let mut off = 0sz;
  let mut cont = true;

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. exists (voff:US.t) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then A.pts_to ht.contents full_perm pht.repr
      else A.pts_to ht.contents full_perm (PHT.delete pht k).repr) **
    pure (
      voff <= sz /\
      all_used_not_by pht.repr (US.v cidx) (US.v voff) k /\
      walk pht.repr (US.v cidx) k (US.v voff) == lookup_repr pht.repr k /\
      delete_repr_walk #s #pht.sz #pht.spec pht.repr k (US.v voff) (US.v cidx) () () == delete_repr #s #pht.sz #pht.spec pht.repr k /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = sz) {
      cont := false;
      assert_ (A.pts_to ht.contents full_perm pht.repr);
    } else {
      let idx = modulo_us sz cidx voff;
      let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment ht.contents idx Zombie #pht.repr;
            cont := false;
            assert_ (pure (pht.repr @@ US.v idx == Used k v'));
            assert_ (pure (Seq.upd pht.repr (US.v idx) Zombie `Seq.equal` (PHT.delete pht k).repr));
          } else {
            off := voff + 1sz;
          } 
        }
        Clean -> {
          cont := false;
          assert_ (pure (pht.repr == (PHT.delete pht k).repr));
        }
        Zombie -> { 
          off := voff + 1sz;
        }
      };
    };
  };
  fold (models s ht (PHT.delete pht k));
}
```