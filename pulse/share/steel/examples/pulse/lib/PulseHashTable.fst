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

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

type pos_us = n:US.t{US.v n > 0}

noeq
type pht_sig_us = {
  keyt : eqtype;
  valt : Type0;
  hashf : keyt -> US.t;
}

noeq
type ht_t (s : pht_sig_us) = {
  sz : pos_us;
  contents : A.larray (cell s.keyt s.valt) (US.v sz);
}

let s_to_ps (s:pht_sig_us) : pht_sig
  = { keyt = s.keyt; valt = s.valt; hashf = (fun k -> US.v (s.hashf k)) }

let models (s:pht_sig_us) (ht:ht_t s) (pht:pht_t (s_to_ps s)) : vprop
= A.pts_to ht.contents full_perm pht.repr `star`
  pure (US.v ht.sz == pht.sz)

let canonical_index_us (#s:pht_sig_us) (k:s.keyt) (sz:pos_us) 
  : US.t = s.hashf k % sz

let modulo_us (v1 v2:US.t) (m:pos_us) (_:squash(US.fits (US.v v1 + US.v v2)))
  : US.t 
  = (v1 + v2) % m

```pulse
fn pulse_lookup_index (#s:pht_sig_us)
                      (#pht:(p:pht_t (s_to_ps s){not_full p.repr}))  
                      (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  returns  o:(o:option (s.valt & US.t){o == PHT.lookup_index_us pht k})
  ensures  models s ht pht
{
  let cidx = canonical_index_us k ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut ret = None #(s.valt & US.t);

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; (voff <= ht.sz && vcont = true)) 
  invariant b. exists (voff:US.t) (vcont:bool). (
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    R.pts_to ret full_perm (if vcont then None else (PHT.lookup_index_us pht k)) **
    pure (
      US.v ht.sz == pht.sz /\
      voff <= ht.sz /\
      walk_get_idx #(s_to_ps s) #pht.sz pht.repr (US.v cidx) k (US.v voff) 
        == lookup_repr_index #(s_to_ps s) #pht.sz pht.repr k /\
      b == (voff <= ht.sz && vcont = true)
    ))
  {
    let voff = !off;
    assume_ (pure (US.fits (US.v cidx + US.v voff)));
    if (voff = ht.sz) {
      cont := false;
      assert (R.pts_to ret full_perm None);
    } else {
      let idx = modulo_us cidx voff ht.sz ();
      let c = op_Array_Index ht.contents idx; 
      match c {
        Used k' v' -> {
          if (k' = k) {
            cont := false;
            write ret (Some (v',idx)) #None;
            assert (pure (pht.repr @@ US.v idx == Used k' v'));
            assert (pure (lookup_repr_index pht.repr k == Some (v', US.v idx)));
          } else {
            off := voff + 1sz;
            assert (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) 
              == walk_get_idx pht.repr (US.v cidx) k (US.v (voff+1sz))));
          }}
        Clean -> {
          cont := false;
          assert (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) == None));
          assert (R.pts_to ret full_perm (PHT.lookup_index_us pht k));
         }
        Zombie -> {
          off := voff + 1sz;
          assert (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) 
            == walk_get_idx pht.repr (US.v cidx) k (US.v (voff+1sz))));
         }
      };
    };
  };
  fold (models s ht pht);
  assert (R.pts_to ret full_perm (PHT.lookup_index_us pht k));
  let o = !ret;
  o
}
```

```pulse
fn lookup (#s:pht_sig_us)
          (#pht:(p:pht_t (s_to_ps s){not_full p.repr}))  
          (ht:ht_t s) (k:s.keyt)
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
fn insert (#s:pht_sig_us)
          (#pht:(p:pht_t (s_to_ps s){not_full p.repr})) 
          (ht:ht_t s) (k:s.keyt) (v:s.valt)
  requires models s ht pht
  ensures  models s ht (PHT.insert pht k v)
{
  let cidx = canonical_index_us k ht.sz;
  let mut off = 0sz;
  let mut cont = true;

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; (voff <= ht.sz && vcont = true)) 
  invariant b. exists (voff:US.t) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    A.pts_to ht.contents full_perm (if vcont then pht.repr else (PHT.insert pht k v).repr) **
    pure (
      US.v ht.sz == pht.sz /\
      voff <= ht.sz /\
      strong_all_used_not_by pht.repr (US.v cidx) (US.v voff) k /\
      walk pht.repr (US.v cidx) k (US.v voff) == lookup_repr pht.repr k /\
      insert_repr_walk #(s_to_ps s) #pht.sz #pht.spec pht.repr k v (US.v voff) (US.v cidx) () () 
        == insert_repr #(s_to_ps s) #pht.sz #pht.spec pht.repr k v /\
      b == (voff <= ht.sz && vcont = true)
    ))
  {
    let voff = !off;
    assume_ (pure (US.fits (US.v cidx + US.v voff)));
    if (voff = ht.sz) {
      cont := false;
      assert (A.pts_to ht.contents full_perm pht.repr);
    } else {
      let idx = modulo_us cidx voff ht.sz ();
      let c = op_Array_Index ht.contents idx #full_perm #pht.repr;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment ht.contents idx (mk_used_cell k v);
            cont := false;
            assert (pure (insert_repr #(s_to_ps s) #pht.sz #pht.spec pht.repr k v `Seq.equal` 
              Seq.upd pht.repr (US.v idx) (mk_used_cell k v))); 
          } else {
            off := voff + 1sz;
          } 
        }
        Clean -> {
          op_Array_Assignment ht.contents idx (mk_used_cell k v);
          cont := false;
          assert (pure (insert_repr #(s_to_ps s) #pht.sz #pht.spec pht.repr k v `Seq.equal` 
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
              assert (pure (insert_repr #(s_to_ps s) #pht.sz #pht.spec pht.repr k v `Seq.equal` 
                Seq.upd (Seq.upd pht.repr (US.v (snd p)) Zombie) (US.v idx) (mk_used_cell k v)));
            }
            None -> { 
              op_Array_Assignment ht.contents idx (mk_used_cell k v); 
              cont := false;
              assert (pure (insert_repr #(s_to_ps s) #pht.sz #pht.spec pht.repr k v 
                `Seq.equal` Seq.upd pht.repr (US.v idx) (mk_used_cell k v)));
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
fn delete (#s:pht_sig_us)
          (#pht:pht_t (s_to_ps s)) 
          (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  ensures  models s ht (PHT.delete pht k)
{
  let cidx = canonical_index_us k ht.sz;
  let mut off = 0sz;
  let mut cont = true;

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; (voff <= ht.sz && vcont = true))
  invariant b. exists (voff:US.t) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    A.pts_to ht.contents full_perm (if vcont then pht.repr else (PHT.delete pht k).repr) **
    pure (
      US.v ht.sz == pht.sz /\
      voff <= ht.sz /\
      all_used_not_by pht.repr (US.v cidx) (US.v voff) k /\
      walk pht.repr (US.v cidx) k (US.v voff) == lookup_repr pht.repr k /\
      delete_repr_walk #(s_to_ps s) #pht.sz #pht.spec pht.repr k (US.v voff) (US.v cidx) () () 
        == delete_repr #(s_to_ps s) #pht.sz #pht.spec pht.repr k /\
      b == (voff <= ht.sz && vcont = true)
    ))
  {
    let voff = !off;
    assume_ (pure (US.fits (US.v cidx + US.v voff)));
    if (voff = ht.sz) {
      cont := false;
      assert (A.pts_to ht.contents full_perm pht.repr);
    } else {
      let idx = modulo_us cidx voff ht.sz ();
      let c = op_Array_Index ht.contents idx #full_perm #pht.repr;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment ht.contents idx Zombie;
            cont := false;
            assert (pure (pht.repr @@ US.v idx == Used k v'));
            assert (pure (Seq.upd pht.repr (US.v idx) Zombie 
              `Seq.equal` (PHT.delete pht k).repr));
          } else {
            off := voff + 1sz;
          } 
        }
        Clean -> {
          cont := false;
          assert (pure (pht.repr == (PHT.delete pht k).repr));
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