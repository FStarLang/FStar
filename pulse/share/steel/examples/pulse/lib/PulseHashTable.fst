module PulseHashTable
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module LK = Pulse.Lib.SpinLock
module PHT = LinearScanHashTable
open LinearScanHashTable
open Pulse.Class.BoundedIntegers

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

```pulse
fn pulse_lookup_index (#s:pht_sig_us)
                      (#pht:erased (pht_t (s_to_ps s)))
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
    A.pts_to ht.contents pht.repr **
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to ret (if vcont then None else (PHT.lookup_index_us pht k)) **
    pure (
      US.v ht.sz == pht_sz pht /\
      voff <= ht.sz /\
      walk_get_idx #(s_to_ps s) #(pht_sz pht) pht.repr (US.v cidx) k (US.v voff) 
        == lookup_repr_index #(s_to_ps s) #(pht_sz pht) pht.repr k /\
      b == (voff <= ht.sz && vcont = true)
    ))
  {
    let voff = !off;
    assume_ (pure (US.fits (US.v cidx + US.v voff)));
    if (voff = ht.sz) {
      cont := false;
      assert (R.pts_to ret None);
    } else {
      let idx = modulo_us cidx voff ht.sz ();
      let c = (ht.contents).(idx); 
      match c {
        Used k' v' -> {
          if (k' = k) {
            cont := false;
            (op_Colon_Equals ret (Some (v',idx)) #None);
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
          assert (R.pts_to ret (PHT.lookup_index_us pht k));
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
  assert (R.pts_to ret (PHT.lookup_index_us pht k));
  let o = !ret;
  o
}
```

```pulse
fn _lookup (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
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
let lookup #s #pht ht k = _lookup #s #pht ht k

```pulse
fn _insert (#s:pht_sig_us)
          (#pht:(p:erased (pht_t (s_to_ps s)){PHT.not_full p.repr}))
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
    R.pts_to off voff **
    R.pts_to cont vcont **
    A.pts_to ht.contents (if vcont then pht.repr else (PHT.insert pht k v).repr) **
    pure (
      US.v ht.sz == pht_sz pht /\
      voff <= ht.sz /\
      strong_all_used_not_by pht.repr (US.v cidx) (US.v voff) k /\
      walk pht.repr (US.v cidx) k (US.v voff) == lookup_repr pht.repr k /\
      insert_repr_walk #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v (US.v voff) (US.v cidx) () () 
        == insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v /\
      b == (voff <= ht.sz && vcont = true)
    ))
  {
    let voff = !off;
    assume_ (pure (US.fits (US.v cidx + US.v voff)));
    if (voff = ht.sz) {
      cont := false;
      assert (A.pts_to ht.contents pht.repr);
    } else {
      let idx = modulo_us cidx voff ht.sz ();
      let c = op_Array_Access ht.contents idx #full_perm #pht.repr;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment ht.contents idx (mk_used_cell k v);
            cont := false;
            assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
              Seq.upd pht.repr (US.v idx) (mk_used_cell k v))); 
          } else {
            off := voff + 1sz;
          } 
        }
        Clean -> {
          op_Array_Assignment ht.contents idx (mk_used_cell k v);
          cont := false;
          assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
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
              assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
                Seq.upd (Seq.upd pht.repr (US.v (snd p)) Zombie) (US.v idx) (mk_used_cell k v)));
            }
            None -> { 
              op_Array_Assignment ht.contents idx (mk_used_cell k v); 
              cont := false;
              assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v 
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
let insert #s #pht ht k v = _insert #s #pht ht k v

```pulse
fn _delete (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
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
    R.pts_to off voff **
    R.pts_to cont vcont **
    A.pts_to ht.contents (if vcont then pht.repr else (PHT.delete pht k).repr) **
    pure (
      US.v ht.sz == pht_sz pht /\
      voff <= ht.sz /\
      all_used_not_by pht.repr (US.v cidx) (US.v voff) k /\
      walk pht.repr (US.v cidx) k (US.v voff) == lookup_repr pht.repr k /\
      delete_repr_walk #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k (US.v voff) (US.v cidx) () () 
        == delete_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k /\
      b == (voff <= ht.sz && vcont = true)
    ))
  {
    let voff = !off;
    assume_ (pure (US.fits (US.v cidx + US.v voff)));
    if (voff = ht.sz) {
      cont := false;
      assert (A.pts_to ht.contents pht.repr);
    } else {
      let idx = modulo_us cidx voff ht.sz ();
      let c = op_Array_Access ht.contents idx #full_perm #pht.repr;
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
let delete #s #pht ht k = _delete #s #pht ht k

```pulse
fn _not_full (#s:pht_sig_us) (#pht:erased (pht_t (s_to_ps s))) (ht:ht_t s)
  requires models s ht pht
  returns b:bool
  ensures models s ht pht ** 
          pure (b ==> PHT.not_full #(s_to_ps s) #(pht_sz pht) pht.repr)
{
  let mut i = 0sz;
  unfold (models s ht pht);

  while (let vi = !i;  
    if (vi < ht.sz) { 
      let c = op_Array_Access ht.contents vi #full_perm #pht.repr; 
      (Used? c) 
    } else { false })
  invariant b. exists (vi:US.t). (
    A.pts_to ht.contents pht.repr **
    R.pts_to i vi **
    pure (
      US.v ht.sz == pht_sz pht /\
      vi <= ht.sz /\
      (b == (vi < ht.sz && Used? (pht.repr @@ (US.v vi)))) /\
      (forall (i:nat). i < US.v vi ==> Used? (pht.repr @@ i))
    )
  )
  {
    let vi = !i;
    i := vi + 1sz;
  };
  let vi = !i;
  let res = vi < ht.sz;
  fold (models s ht pht);
  res
}
```
let not_full #s #pht ht = _not_full #s #pht ht
