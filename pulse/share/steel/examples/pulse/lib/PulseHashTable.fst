module PulseHashTable
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module LK = Pulse.Lib.SpinLock
module U64 = FStar.UInt64
module PHT = LinearScanHashTable
open LinearScanHashTable
open Pulse.Class.BoundedIntegers

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let canonical_index_us (#s:pht_sig_us) (k:s.keyt) (sz:pos_us) 
  : US.t = s.hashf k % sz

let modulo_us (v1 v2:US.t) (m:pos_us) (_:squash(US.fits (US.v v1 + US.v v2)))
  : US.t 
  = (v1 + v2) % m

```pulse
fn add_us (v1 v2:US.t) 
  requires emp
  returns o:option US.t
  ensures pure ( match o with
    | Some v -> US.v v = US.v v1 + US.v v2 /\ US.fits (US.v v)
    | None -> true )
{
  admit()
  // let b = pow2 U64.n - US.v v1 > US.v v2;
  // if b {
  //   assert (fits (US.v v1 + US.v v2));
  //   let v = v1 + v2;
  //   Some v
  // } else {
  //   None
  // }
}
```

```pulse
fn pulse_lookup_index (#s:pht_sig_us)
                      (#pht:erased (pht_t (s_to_ps s)))
                      (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  returns  p:bool & option (s.valt & US.t)
  ensures  models s ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup_index_us pht k )
{
  let cidx = canonical_index_us k ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;
  let mut ret = None #(s.valt & US.t);

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; let verr = !err; (voff <= ht.sz && vcont = true && verr = false)) 
  invariant b. exists (voff:US.t) (vcont verr:bool). (
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    R.pts_to err full_perm verr **
    R.pts_to ret full_perm (if (vcont || verr) then None else (PHT.lookup_index_us pht k)) **
    pure (
      US.v ht.sz == pht_sz pht /\
      voff <= ht.sz /\
      walk_get_idx #(s_to_ps s) #(pht_sz pht) pht.repr (US.v cidx) k (US.v voff) 
        == lookup_repr_index #(s_to_ps s) #(pht_sz pht) pht.repr k /\
      b == (voff <= ht.sz && vcont = true && verr = false)
    ))
  {
    let voff = !off;
    if (voff = ht.sz) {
      cont := false;
      assert (R.pts_to ret full_perm None);
    } else {
      let o = add_us cidx voff;
      match o {
      Some v -> {
      let idx = v % ht.sz;
        let c = op_Array_Access ht.contents idx; 
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
          assert (R.pts_to ret full_perm (PHT.lookup_index_us pht k));
        }
        Zombie -> {
          off := voff + 1sz;
          assert (pure (walk_get_idx pht.repr (US.v cidx) k (US.v voff) 
            == walk_get_idx pht.repr (US.v cidx) k (US.v (voff+1sz))));
        }
      }}
      None -> { err := true; }
  }}};
  let verr = !err;
  let o = !ret;
  fold (models s ht pht);
  if verr {
    (false,o)
  } else {
    assert (R.pts_to ret full_perm (PHT.lookup_index_us pht k));
    (true,o)
  }
}
```

```pulse
fn _lookup (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
          (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  returns  p:bool & option s.valt
  ensures  models s ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup pht k )
{
  let p = pulse_lookup_index #s #pht ht k;
  if (fst p) {
    match (snd p) {
      Some p -> { (true, Some (fst p)) }
      None -> { (true, None #s.valt) }
    }
  } else {
    (false, None #s.valt)
  }
}
```
let lookup #s #pht ht k = _lookup #s #pht ht k

```pulse
fn _insert (#s:pht_sig_us)
          (#pht:(p:erased (pht_t (s_to_ps s)){PHT.not_full p.repr}))
          (ht:ht_t s) (k:s.keyt) (v:s.valt)
  requires models s ht pht
  returns b:bool
  ensures `@(if b then models s ht (PHT.insert pht k v) else models s ht pht)
{
  let cidx = canonical_index_us k ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; let verr = !err; (voff <= ht.sz && vcont = true && verr = false)) 
  invariant b. exists (voff:US.t) (vcont verr:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    R.pts_to err full_perm verr **
    A.pts_to ht.contents full_perm (if (vcont || verr) then pht.repr else (PHT.insert pht k v).repr) **
    pure (
      US.v ht.sz == pht_sz pht /\
      voff <= ht.sz /\
      strong_all_used_not_by pht.repr (US.v cidx) (US.v voff) k /\
      walk pht.repr (US.v cidx) k (US.v voff) == lookup_repr pht.repr k /\
      insert_repr_walk #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v (US.v voff) (US.v cidx) () () 
        == insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v /\
      b == (voff <= ht.sz && vcont = true && verr = false)
    ))
  {
    let voff = !off;
    if (voff = ht.sz) {
      cont := false;
      assert (A.pts_to ht.contents full_perm pht.repr);
    } else {
      let o = add_us cidx voff;
      match o {
      Some v -> {
        let idx = v % ht.sz;
        let c = op_Array_Access ht.contents idx #full_perm #pht.repr;
        match c {
        Used k' v' -> { 
          if (k' = k) {
            assert (A.pts_to ht.contents full_perm pht.repr);
            assert (pure ( US.v idx < Seq.length pht.repr));
            admit()
            // op_Array_Assignment ht.contents idx (mk_used_cell k v);
            // cont := false;
            // assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
            //   Seq.upd pht.repr (US.v idx) (mk_used_cell k v))); 
          } else {
            off := voff + 1sz;
          } 
        }
        Clean -> {
          admit()
          // op_Array_Assignment ht.contents idx (mk_used_cell k v);
          // cont := false;
          // assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
          //   Seq.upd pht.repr (US.v idx) (mk_used_cell k v)));
        }
        Zombie -> {
          fold (models s ht pht);
          let res = pulse_lookup_index #s #pht ht k;
          unfold (models s ht pht);
          if (fst res) {
            let o = snd res;
            match o {
              Some p -> {
                op_Array_Assignment ht.contents (snd p) Zombie;
                admit()
                // op_Array_Assignment ht.contents idx (mk_used_cell k v);
                // cont := false;
                // assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
                //   Seq.upd (Seq.upd pht.repr (US.v (snd p)) Zombie) (US.v idx) (mk_used_cell k v)));
              }
              None -> { 
                admit()
                // op_Array_Assignment ht.contents idx (mk_used_cell k v); 
                // cont := false;
                // assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v 
                //   `Seq.equal` Seq.upd pht.repr (US.v idx) (mk_used_cell k v)));
              }
          }} else {
            // ERROR - lookup failed
            err := true;
          }
        }
      }
    }
    None -> { err := true }}}
  };
  let verr = !err;
  if verr {
    fold (models s ht pht);
    false
  } else {
    fold (models s ht (PHT.insert pht k v));
    true
  }
}
```
let insert #s #pht ht k v = _insert #s #pht ht k v

```pulse
fn _delete (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
          (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  returns b:bool
  ensures `@(if b then models s ht (PHT.delete pht k) else models s ht pht)
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
      assert (A.pts_to ht.contents full_perm pht.repr);
    } else {
      let o = add_us cidx voff;
      match o {
      Some v -> {
        let idx = v % ht.sz;
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
      }
    }
    None -> { false }}}
  };
  fold (models s ht (PHT.delete pht k));
  true
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
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to i full_perm vi **
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
