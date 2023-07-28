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

```pulse
fn pulse_lookup_index (#s:pht_sig) (#pht:(p:pht s{not_full p.repr}))  
                (ht:ht s) (k:s.keyt)
  requires models s pht ht
  returns  o:(o:option (s.valt & nat){o == PHT.lookup_index pht k})
  ensures  models s pht ht
{
  let sz = ht.sz;
  let cidx = canonical_index k sz;
  let mut off = coerce_nat 0;
  let mut cont = true;
  let mut ret = None #(s.valt & nat);

  unfold (models s pht ht);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true)) 
  invariant b. exists (voff:nat) (vcont:bool). (
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then R.pts_to ret full_perm None
      else R.pts_to ret full_perm (PHT.lookup_index pht k)) ** 
    pure (
      pht.sz == sz /\
      sz > 0 /\
      voff >= 0 /\ voff <= sz /\
      walk_get_idx pht.repr cidx k voff == lookup_repr_index pht.repr k /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = sz) {
      cont := false;
      assert_ (R.pts_to ret full_perm None);
      assert_ (pure (walk_get_idx pht.repr cidx k voff == None));
      ()
    } else {
      let idx = (cidx+voff)%sz;
      let c = op_Array_Index_nat ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            cont := false;
            write ret (Some (v',idx)) #None;
            assert_ (pure (pht.repr @@ idx == Used k' v'));
            assert_ (pure (lookup_repr_index pht.repr k == Some (v', idx)));
            ()
          } else {
            off := voff + 1;
            assert_ (pure (walk_get_idx pht.repr cidx k voff == walk_get_idx pht.repr cidx k (voff+1)));
            ()
          }}
        Clean -> {
          cont := false;
          assert_ (pure (walk_get_idx pht.repr cidx k voff == None));
          assert_ (R.pts_to ret full_perm (lookup_repr_index #s #pht.sz pht.repr k));
          ()
         }
        Zombie -> {
          off := voff + 1;
          assert_ (pure (walk_get_idx pht.repr cidx k voff == walk_get_idx pht.repr cidx k (voff+1)));
          ()
         }
      };
    };
  };
  fold (models s pht ht);
  assert_ (R.pts_to ret full_perm (lookup_repr_index #s #pht.sz pht.repr k));
  let o = !ret;
  o
}
```

```pulse
fn lookup (#s:pht_sig) (#pht:(p:pht s{not_full p.repr}))  
          (ht:ht s) (k:s.keyt)
  requires models s pht ht
  returns  o:(o:option s.valt{o == PHT.lookup pht k})
  ensures  models s pht ht
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
  requires models s pht ht
  ensures  models s (PHT.insert pht k v) ht
{
  let sz = ht.sz;
  let a = ht.contents;
  let cidx = canonical_index k sz;
  let mut off = coerce_nat 0;
  let mut cont = true;

  unfold (models s pht ht);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. exists (voff:nat) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then A.pts_to ht.contents full_perm pht.repr
      else A.pts_to ht.contents full_perm (PHT.insert pht k v).repr) **
    pure (
      voff >= 0 /\ voff <= sz /\
      strong_all_used_not_by pht.repr cidx voff k /\
      walk pht.repr cidx k voff == lookup_repr pht.repr k /\
      insert_repr_walk #s #sz #pht.spec pht.repr k v voff cidx () () == insert_repr #s #sz #pht.spec pht.repr k v /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = sz) {
      // this case is not reachable, needs proof?
      ()
    } else {
      let idx = (cidx+voff)%sz;
      let c = op_Array_Index_nat ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment_nat ht.contents idx (mk_used_cell k v);
            cont := false;
            assert_ (pure (insert_repr #s #sz #pht.spec pht.repr k v `Seq.equal` 
              Seq.upd pht.repr idx (mk_used_cell k v))); 
            ()
          } else {
            off := voff + 1;
            ()
          } 
        }
        Clean -> {
          op_Array_Assignment_nat ht.contents idx (mk_used_cell k v);
          cont := false;
          assert_ (pure (insert_repr #s #sz #pht.spec pht.repr k v `Seq.equal` 
            Seq.upd pht.repr idx (mk_used_cell k v)));
          ()
        }
        Zombie -> {
          fold (models s pht ht);
          let o = pulse_lookup_index #s #pht ht k;
          unfold (models s pht ht);
          match o {
            Some p -> {
              op_Array_Assignment_nat ht.contents (snd p) Zombie;
              op_Array_Assignment_nat ht.contents idx (mk_used_cell k v);
              cont := false;
              assert_ (pure (insert_repr #s #sz #pht.spec pht.repr k v `Seq.equal` 
                Seq.upd (Seq.upd pht.repr (snd p) Zombie) idx (mk_used_cell k v)));
              ()
            }
            None -> { 
              op_Array_Assignment_nat ht.contents idx (mk_used_cell k v); 
              cont := false;
              assert_ (pure (insert_repr #s #sz #pht.spec pht.repr k v `Seq.equal` Seq.upd pht.repr idx (mk_used_cell k v)));
              ()
            }
          };
        }
      };
    };
  };
  fold (models s (PHT.insert pht k v) ht);
  ()
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

  unfold (models s pht ht);

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. exists (voff:nat) (vcont:bool). (
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    `@(if vcont 
      then A.pts_to ht.contents full_perm pht.repr
      else A.pts_to ht.contents full_perm (PHT.delete pht k).repr) **
    pure (
      voff >= 0 /\ voff <= sz /\
      all_used_not_by pht.repr cidx voff k /\
      walk pht.repr cidx k voff == lookup_repr pht.repr k /\
      delete_repr_walk #s #sz #pht.spec pht.repr k voff cidx () () == delete_repr #s #sz #pht.spec pht.repr k /\
      b == (voff <= sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff=sz) {
      ()
    } else {
      let idx = (cidx+voff)%sz;
      let c = op_Array_Index_nat ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            op_Array_Assignment_nat ht.contents idx Zombie;
            cont := false;
            assert_ (pure (pht.repr @@ idx == Used k v'));
            assert_ (pure (Seq.upd pht.repr idx Zombie `Seq.equal` (PHT.delete pht k).repr));
            ()
          } else {
            off := voff + 1;
            ()
          } 
        }
        Clean -> {
          cont := false;
          assert_ (pure (pht.repr == (PHT.delete pht k).repr));
          ()
        }
        Zombie -> { 
          off := voff + 1;
          () 
        }
      };
    };
  };
  fold (models s (PHT.delete pht k) ht);
  ()
}
```