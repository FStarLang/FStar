module Pulse.Lib.HashTable
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module PHT = Pulse.Lib.HashTable.Spec
// open Pulse.Lib.BoundedIntegers

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let related #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt) : prop =
    SZ.v ht.sz == pht.repr.sz /\
    pht.repr.hashf == lift_hash_fun ht.hashf

let models #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt) : vprop
= A.pts_to ht.contents pht.repr.seq **
  pure (
    related ht pht /\
    A.is_full_array ht.contents
  )


```pulse
fn alloc' (#k:eqtype) (#v:Type0) (hashf:(k -> US.t)) (l:pos_us)
  requires emp
  returns ht:ht_t k v
  ensures exists pht. models ht pht ** pure (pht == mk_init_pht hashf l)
{
  let contents = A.alloc #(cell k v) Clean l;
  let ht = mk_ht l hashf contents;
  let pht = Ghost.hide (mk_init_pht #k #v hashf l);
  rewrite (A.pts_to contents (Seq.create (SZ.v l) Clean))
       as (A.pts_to ht.contents pht.repr.seq);
  fold (models ht pht);
  ht
}
```
let alloc = alloc'

```pulse
fn dealloc' (#k:eqtype) (#v:Type0) (ht:ht_t k v)
  requires exists pht. models ht pht
  ensures emp
{
  open SZ;
  let mut off = 0sz;
  with pht. assert (models ht pht);
  unfold (models ht pht);
  A.free ht.contents;
}
```
let dealloc = dealloc'

let sz_add (x y : SZ.t)
  : o:option SZ.t { Some? o ==> SZ.v (Some?.v o) == SZ.v x + SZ.v y } 
  = let open SZ in
    if x <=^ 0xffffsz
    then (
      if (y <=^ 0xffffsz -^ x)
      then Some (x +^ y)
      else None
    )
    else None


let size_t_mod (x:SZ.t) (y : SZ.t { y =!= 0sz }) 
  : z:SZ.t { SZ.v z == SZ.v x % SZ.v y }
  = SZ.(x %^ y)

#push-options "--z3rlimit_factor 4 --query_stats"
```pulse
fn pulse_lookup_index (#kt:eqtype) (#vt:Type0)
                      (ht:ht_t kt vt) (k:kt)
                      (#pht:erased (pht_t kt vt))
  requires models ht pht
  returns  p:bool & option (vt & SZ.t)
  ensures  models ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup_index_us pht k )
{
  open SZ;
  let cidx = size_t_mod (ht.hashf k) ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;
  let mut ret = None #(vt & SZ.t);
  unfold (models ht pht);
  while (let voff = !off;
         let vcont = !cont;
         let verr = !err; 
         (voff <=^ ht.sz && vcont = true && verr = false)) 
  invariant b. exists (voff:SZ.t) (vcont verr:bool). (
    A.pts_to ht.contents pht.repr.seq **
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    R.pts_to ret (if (vcont || verr) then None else (PHT.lookup_index_us pht k)) **
    pure (
      US.v ht.sz == pht_sz pht /\
      voff <=^ ht.sz /\
      walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) 
        == lookup_repr_index pht.repr k /\
      b == (voff <=^ ht.sz && vcont = true && verr = false)
    ))
  {
    let voff = !off;
    if (voff = ht.sz)
    {
      cont := false;
      assert (R.pts_to ret None);
    }
    else
    {
      let opt_sum = cidx `sz_add` voff;
      match opt_sum
      {
        Some sum -> 
        {
          let idx = size_t_mod sum ht.sz;
          let c = ht.contents.(idx); 
          match c
          {
            Used k' v' ->
            {
              if (k' = k)
              {
                cont := false;
                ret := Some (v', idx);
                assert (pure (pht.repr @@ SZ.v idx == Used k' v'));
                assert (pure (lookup_repr_index pht.repr k == Some (v', SZ.v idx)));
              } else
              {
                off := voff +^ 1sz;
                assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) 
                  == walk_get_idx pht.repr (SZ.v cidx) k (SZ.v (voff+^1sz))));
              }
            }
            Clean ->
            {
              cont := false;
              assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) == None));
              assert (R.pts_to ret (PHT.lookup_index_us pht k));
            }
            Zombie ->
            {
              off := voff +^ 1sz;
              assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) 
                == walk_get_idx pht.repr (SZ.v cidx) k (SZ.v (voff+^1sz))));
            }
          }
        }
        None ->
        { 
          // ERROR - add failed
          err := true; 
        }
      }
    }
  };
  let verr = !err;
  let o = !ret;
  fold (models ht pht);
  if verr
  {
    (false,o)
  }
  else
  {
    assert (R.pts_to ret (PHT.lookup_index_us pht k));
    (true,o)
  }
}
```

#pop-options
```pulse
fn lookup' (#kt:eqtype) (#vt:Type0)
           (ht:ht_t kt vt) (k:kt)
           (#pht:erased (pht_t kt vt))
  requires models ht pht
  returns  p:bool & option vt
  ensures  models ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup pht k )
{
  let p = pulse_lookup_index ht k;
  if (fst p)
  {
    match (snd p)
    {
      Some p -> { (true, Some (fst p)) }
      None -> { (true, None #vt) }
    }
  } 
  else
  {
    (false, None #vt)
  }
}
```
let lookup = lookup'

```pulse
fn insert' (#kt:eqtype) (#vt:Type0)
           (ht:ht_t kt vt) (k:kt) (v:vt)
           (#pht:(p:erased (pht_t kt vt){PHT.not_full p.repr}))
  requires models ht pht
  returns b:bool
  ensures exists pht'. 
    models ht pht' **
    pure (if b
          then pht'==PHT.insert pht k v
          else pht'==pht)
{
  let cidx = size_t_mod (ht.hashf k) ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;

  unfold (models ht pht);
  while
  (
    let vcont = !cont;
    let verr = !err;
    (vcont = true && verr = false)
  ) 
  invariant b. exists (voff:SZ.t) (vcont verr:bool). (
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    A.pts_to ht.contents (if (vcont || verr) then pht.repr.seq else (PHT.insert pht k v).repr.seq) **
    pure (
      related ht pht /\
      SZ.(voff <=^ ht.sz) /\
      strong_all_used_not_by pht.repr (SZ.v cidx) (SZ.v voff) k /\
      walk pht.repr (SZ.v cidx) k (SZ.v voff) == lookup_repr pht.repr k /\
      insert_repr_walk #kt #vt #(pht_sz pht) #pht.spec pht.repr k v (SZ.v voff) (SZ.v cidx) () () 
        == insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v /\
      b == (vcont = true && verr = false)
    ))
  {
    let voff = !off;
    if (voff = ht.sz)
    {
      cont := false;
      full_not_full pht.repr k;
      // elim_false unit (fun _ -> A.pts_to ht.contents pht.repr.seq);
      assert (A.pts_to ht.contents pht.repr.seq);
    }
    else
    {
      let opt_sum = cidx `sz_add` voff;
      match opt_sum
      {
        Some sum ->
        {
          let idx = size_t_mod sum ht.sz;
          let c = (ht.contents).(idx); 
          match c
          {
            Used k' v' -> { 
              if (k' = k) {
                assert (A.pts_to ht.contents pht.repr.seq);
                assert (pure ( SZ.v idx < Seq.length pht.repr.seq));
                ht.contents.(idx) <- (mk_used_cell k v);
                cont := false;
                assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal` 
                              Seq.upd pht.repr.seq (SZ.v idx) (mk_used_cell k v))); 
              } else {
                off := SZ.(voff +^ 1sz);
              } 
            }
            Clean -> {
              ht.contents.(idx) <- (mk_used_cell k v);
              cont := false;
              assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal` 
                      Seq.upd pht.repr.seq (SZ.v idx) (mk_used_cell k v)));
            }
            Zombie ->
            {
              fold (models ht pht);
              let res = pulse_lookup_index ht k;
              unfold (models ht pht);
              if (fst res)
              {
                let o = snd res;
                match o
                {
                  Some p ->
                  {
                    ((ht.contents).(snd p) <- Zombie);
                    ((ht.contents).(idx) <- (mk_used_cell k v));
                    cont := false;
                    assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal` 
                                  Seq.upd (Seq.upd pht.repr.seq (SZ.v (snd p)) Zombie) (SZ.v idx) (mk_used_cell k v)));
                  }
                  None ->
                  { 
                    ((ht.contents).(idx) <- (mk_used_cell k v)); 
                    cont := false;
                    assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal`
                                  Seq.upd pht.repr.seq (SZ.v idx) (mk_used_cell k v)));
                  }
                }
              }
              else
              {
                // ERROR - lookup failed
                err := true;
              }
            }
          }
        }
        None ->
        {
          // ERROR - add failed
          err := true 
        }
      }
    }
  };
  let verr = !err;
  if verr
  {
    fold (models ht pht);
    false
  } else {
    assert (A.pts_to ht.contents (PHT.insert pht k v).repr.seq);
    fold (models ht (PHT.insert pht k v));
    true
  }
}
```

let insert = insert'

```pulse
fn delete' (#kt:eqtype) (#vt:Type0)
           (ht:ht_t kt vt) (k:kt)
           (#pht:erased (pht_t kt vt))
  requires models ht pht
  returns b:bool
  ensures exists pht'. 
    models ht pht' **
    pure (if b then pht' == PHT.delete pht k else pht' == pht)
{
  let cidx = size_t_mod (ht.hashf k) ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;

  unfold (models ht pht);
  while 
  (
    let vcont = !cont;
    let verr = !err; 
    (vcont = true && verr = false)
  )
  invariant b. exists (voff:SZ.t) (vcont verr:bool). (
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    A.pts_to ht.contents (if (vcont || verr) then pht.repr.seq else (PHT.delete pht k).repr.seq) **
    pure (
      SZ.v ht.sz == pht_sz pht /\
      SZ.(voff <=^ ht.sz) /\
      all_used_not_by pht.repr (SZ.v cidx) (SZ.v voff) k /\
      walk pht.repr (SZ.v cidx) k (SZ.v voff) == lookup_repr pht.repr k /\
      delete_repr_walk #kt #vt #(pht_sz pht) #pht.spec pht.repr k (SZ.v voff) (SZ.v cidx) () () 
        == delete_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k /\
      b == (vcont = true && verr = false)
    ))
  {
    let voff = !off;
    if (voff = ht.sz)
    {
      cont := false;
      assert (A.pts_to ht.contents pht.repr.seq);
    }
    else
    {
      let opt_sum = cidx `sz_add` voff;
      match opt_sum
      {
        Some sum ->
        {
          let idx = size_t_mod sum ht.sz;
          let c = ht.contents.(idx); 
          match c
          {
            Used k' v' ->
            { 
              if (k' = k)
              {
                ht.contents.(idx) <- Zombie;
                cont := false;
                assert (pure (pht.repr @@ SZ.v idx == Used k v'));
                assert (pure (Seq.upd pht.repr.seq (SZ.v idx) Zombie 
                  `Seq.equal` (PHT.delete pht k).repr.seq));
              }
              else
              {
                off := SZ.(voff +^ 1sz);
              } 
            }
            Clean ->
            {
              cont := false;
              assert (pure (pht.repr == (PHT.delete pht k).repr));
            }
            Zombie ->
            {
              off := SZ.(voff +^ 1sz);
            }
          }
        }
        None ->
        {
          // ERROR - add failed
          err := false 
        }
      }
    }
  };
  let verr = !err;
  if verr
  {
    fold (models ht pht);
    false
  }
  else
  {
    fold (models ht (PHT.delete pht k));
    true
  }
}
```
let delete = delete'

```pulse
fn not_full' (#kt:eqtype) (#vt:eqtype)
             (ht:ht_t kt vt)
             (#pht:erased (pht_t kt vt))
  requires models ht pht
  returns b:bool
  ensures models ht pht ** 
          pure (b ==> PHT.not_full pht.repr)
{
  let mut i = 0sz;
  unfold (models ht pht);
  while
  (
    let vi = !i;  
    if SZ.(vi <^ ht.sz) 
    { 
      let c = ht.contents.(vi); 
      (Used? c) 
    }
    else 
    { 
      false
    }
  )
  invariant b. exists (vi:SZ.t). (
    A.pts_to ht.contents pht.repr.seq **
    R.pts_to i vi **
    pure (
      SZ.v ht.sz == pht_sz pht /\
      SZ.(vi <=^ ht.sz) /\
      (b == (SZ.(vi <^ ht.sz) && Used? (pht.repr @@ (SZ.v vi)))) /\
      (forall (i:nat). i < SZ.v vi ==> Used? (pht.repr @@ i))
    )
  )
  {
    let vi = !i;
    i := SZ.(vi +^ 1sz);
  };
  let vi = !i;
  let res = SZ.(vi <^ ht.sz);
  fold (models ht pht);  
  res
}
```
let not_full = not_full'


let hash_us (k:US.t) : US.t= k

let init_not_full (#kt:eqtype) (#vt:eqtype) (hashf:kt -> US.t) (l:pos_us)
  : Lemma (Pulse.Lib.HashTable.Spec.not_full (mk_init_pht #kt #vt hashf l).repr)
  = assert (~(Used? ((mk_init_pht #kt #vt hashf l).repr @@ 0)))
  
```pulse
fn test_mono' (_:unit)
  requires emp
  ensures emp
{
   let ht = alloc #US.t #US.t hash_us 128sz;
   init_not_full #US.t #US.t hash_us 128sz;
   let b = insert' ht 0sz 17sz;
   if (b) {
     let v = lookup ht 0sz;
     if (fst v) {
       assert pure (snd v == Some 17sz);
       dealloc ht
     }
     else {
      dealloc ht
     }
   }
   else {
    let b = delete ht 0sz;
    let b' = not_full ht;
    dealloc ht
   } 
}
```
let test_mono = test_mono'


