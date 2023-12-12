module Pulse.Lib.HashTable
open Pulse.Lib.Pervasives
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module PHT = Pulse.Lib.HashTable.Spec

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let related #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt) : prop =
    SZ.v ht.sz == pht.repr.sz /\
    pht.repr.hashf == lift_hash_fun ht.hashf

let models #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt) : vprop
= V.pts_to ht.contents pht.repr.seq **
  pure (
    related ht pht /\
    V.is_full_vec ht.contents
  )

type exploded_refs (k:eqtype) (v:Type0) =
  ref pos_us &
  ref (k -> US.t) &
  ref (V.vec (cell k v))

let tfst (x:'a & 'b & 'c) : 'a = Mktuple3?._1 x
let tsnd (x:'a & 'b & 'c) : 'b = Mktuple3?._2 x
let tthd (x:'a & 'b & 'c) : 'c = Mktuple3?._3 x

let token (#k:eqtype) (#v:Type0) (r:ref (ht_t k v)) (res:exploded_refs k v) : vprop =
  exists* ht. pts_to r ht

let exploded_vp (#k:eqtype) (#v:Type0) (r:ref (ht_t k v)) (ht:ht_t k v) (res:exploded_refs k v) : vprop =
  pts_to (tfst res) ht.sz **
  pts_to (tsnd res) ht.hashf **
  pts_to (tthd res) ht.contents **
  token r res

```pulse
fn explode_ref (#k:eqtype) (#v:Type0) (#ht:erased (ht_t k v)) (r:ref (ht_t k v))
  requires pts_to r ht
  returns res:exploded_refs k v
  ensures exploded_vp r ht res
{
  let htc = !r;
  let r_sz = alloc htc.sz;
  let r_hashf = alloc htc.hashf;
  let r_contents = alloc htc.contents;
  let res = (r_sz, r_hashf, r_contents);
  rewrite each r_sz as (tfst res),
               r_hashf as (tsnd res),
               r_contents as (tthd res);
  fold (token r res);
  fold (exploded_vp r ht res);
  res  
}
```

```pulse
fn unexplode_ref (#k:eqtype) (#v:Type0) (#ht:erased (ht_t k v))
  (r:ref (ht_t k v))
  (res:exploded_refs k v)
  requires exploded_vp r ht res
  ensures pts_to r ht
{
  unfold (exploded_vp r ht res);
  unfold (token r res);
  let sz = !(tfst res);
  let hashf = !(tsnd res);
  let contents = !(tthd res);
  free (tfst res); free (tsnd res); free (tthd res);
  let s = mk_ht sz hashf contents;
  r := s
}
```

```pulse
fn alloc (#k:eqtype) (#v:Type0) (hashf:(k -> US.t)) (l:pos_us)
  requires emp
  returns ht:ht_t k v
  ensures exists pht. models ht pht ** pure (pht == mk_init_pht hashf l)
{
  let contents = V.alloc #(cell k v) Clean l;
  let ht = mk_ht l hashf contents;
  let pht = Ghost.hide (mk_init_pht #k #v hashf l);
  rewrite (V.pts_to contents (Seq.create (SZ.v l) Clean))
       as (V.pts_to ht.contents pht.repr.seq);
  fold (models ht pht);
  ht
}
```

```pulse
fn dealloc (#k:eqtype) (#v:Type0) (ht:ht_t k v)
  requires exists pht. models ht pht
  ensures emp
{
  open SZ;
  let mut off = 0sz;
  with pht. assert (models ht pht);
  unfold (models ht pht);
  V.free ht.contents;
}
```

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

assume val ref_apply (#a #b:Type) (#f:erased (a -> b)) (r:ref (a -> b)) (x:a)
  : stt b
    (requires pts_to r f)
    (ensures fun y -> pts_to r f ** pure (y == (reveal f) x))

assume val vec_ref_read (#a:Type0) (r:ref (V.vec a))
  (i:SZ.t)
  (#v:erased (V.vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  : stt a
    (requires pts_to r v ** V.pts_to v s)
    (ensures fun res -> pts_to r v ** V.pts_to v s ** pure (res == Seq.index s (SZ.v i)))

assume val vec_ref_write (#a:Type0) (r:ref (V.vec a))
  (i:SZ.t)
  (x:a)
  (#v:erased (V.vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  : stt unit
    (requires pts_to r v ** V.pts_to v s)
    (ensures fun _ -> pts_to r v ** V.pts_to v (Seq.upd s (SZ.v i) x))


#push-options "--z3rlimit_factor 4 --query_stats"
```pulse
fn pulse_lookup_index (#kt:eqtype) (#vt:Type0)
  (#ht:erased (ht_t kt vt))
  (#pht:erased (pht_t kt vt))
  (r:ref (ht_t kt vt))
  (res:exploded_refs kt vt)
  (k:kt)
  requires exploded_vp r ht res ** models ht pht
  returns  p:bool & option (vt & SZ.t)
  ensures  exploded_vp r ht res ** models ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup_index_us pht k )
{
  open SZ;

  unfold (exploded_vp r ht res);
  let sz = !(tfst res);
  let hash = ref_apply (tsnd res) k;
  fold (exploded_vp r ht res);

  let cidx = size_t_mod hash sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;
  let mut ret = None #(vt & SZ.t);
  unfold (models ht pht);

  while (let voff = !off;
         let vcont = !cont;
         let verr = !err; 
         (voff <=^ sz && vcont = true && verr = false)) 
  invariant b. exists (voff:SZ.t) (vcont verr:bool). (
    exploded_vp r ht res **
    V.pts_to ht.contents pht.repr.seq **
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
    unfold (exploded_vp r ht res);
    let voff = !off;
    if (voff = sz)
    {
      cont := false;
      assert (R.pts_to ret None);
      fold (exploded_vp r ht res);
    }
    else
    {
      let opt_sum = cidx `sz_add` voff;
      match opt_sum
      {
        Some sum -> 
        {
          let idx = size_t_mod sum sz;
          rewrite (V.pts_to ht.contents pht.repr.seq)
               as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
          let c = vec_ref_read (tthd res) idx;
          rewrite (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)))
               as (V.pts_to ht.contents pht.repr.seq);
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
                fold (exploded_vp r ht res);
              } else
              {
                off := voff +^ 1sz;
                assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) 
                  == walk_get_idx pht.repr (SZ.v cidx) k (SZ.v (voff+^1sz))));
                fold (exploded_vp r ht res);
              }
            }
            Clean ->
            {
              cont := false;
              assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) == None));
              assert (R.pts_to ret (PHT.lookup_index_us pht k));
              fold (exploded_vp r ht res);
            }
            Zombie ->
            {
              off := voff +^ 1sz;
              assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) 
                == walk_get_idx pht.repr (SZ.v cidx) k (SZ.v (voff+^1sz))));
              fold (exploded_vp r ht res);
            }
          }
        }
        None ->
        { 
          // ERROR - add failed
          err := true;
          fold (exploded_vp r ht res);
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
fn lookup (#kt:eqtype) (#vt:Type0)
  (r:ref (ht_t kt vt)) (k:kt)
  (#ht:erased (ht_t kt vt))
  (#pht:erased (pht_t kt vt))
  requires pts_to r ht ** models ht pht
  returns  p:bool & option vt
  ensures  pts_to r ht ** models ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup pht k )
{
  let res = explode_ref r;
  let p = pulse_lookup_index r res k;
  unexplode_ref r res;
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

```pulse
fn insert (#kt:eqtype) (#vt:Type0)
  (r:ref (ht_t kt vt)) (k:kt) (v:vt)
  (#ht:erased (ht_t kt vt))
  (#pht:(p:erased (pht_t kt vt) { PHT.not_full p.repr }))
  
  requires pts_to r ht ** models ht pht
  returns b:bool
  ensures exists ht' pht'.
    pts_to r ht' ** models ht' pht' **
    pure (if b
          then pht'== PHT.insert pht k v
          else pht'== pht)
{
  let res = explode_ref r;

  unfold (exploded_vp r ht res);
  let sz = !(tfst res);
  let hash = ref_apply (tsnd res) k;
  fold (exploded_vp r ht res);

  let cidx = size_t_mod hash sz;
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
    exploded_vp r ht res **
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    V.pts_to ht.contents (if (vcont || verr) then pht.repr.seq else (PHT.insert pht k v).repr.seq) **
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
    unfold (exploded_vp r ht res);
    let voff = !off;
    if (voff = sz)
    {
      cont := false;
      full_not_full pht.repr k;
      assert (V.pts_to ht.contents pht.repr.seq);
      fold (exploded_vp r ht res);
    }
    else
    {
      let opt_sum = cidx `sz_add` voff;
      match opt_sum
      {
        Some sum ->
        {
          let idx = size_t_mod sum sz;
          rewrite (V.pts_to ht.contents pht.repr.seq)
               as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
          let c = vec_ref_read (tthd res) idx;
          rewrite (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)))
               as (V.pts_to ht.contents pht.repr.seq);

          match c
          {
            Used k' v' -> { 
              if (k' = k) {
                assert (V.pts_to ht.contents pht.repr.seq);
                assert (pure ( SZ.v idx < Seq.length pht.repr.seq));
                rewrite (V.pts_to ht.contents pht.repr.seq)
                     as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
                vec_ref_write (tthd res) idx (mk_used_cell k v);
                assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal` 
                              Seq.upd pht.repr.seq (SZ.v idx) (mk_used_cell k v)));
                rewrite (V.pts_to (reveal (hide ht.contents)) (Seq.upd (reveal (hide pht.repr.seq)) (SZ.v idx) (mk_used_cell k v)))
                     as (V.pts_to ht.contents (insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq);
                cont := false;
                fold (exploded_vp r ht res);
              } else {
                off := SZ.(voff +^ 1sz);
                fold (exploded_vp r ht res);
              } 
            }
            Clean -> {
              rewrite (V.pts_to ht.contents pht.repr.seq)
                   as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
              vec_ref_write (tthd res) idx (mk_used_cell k v);
              assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal` 
                            Seq.upd pht.repr.seq (SZ.v idx) (mk_used_cell k v)));
              rewrite (V.pts_to (reveal (hide ht.contents)) (Seq.upd (reveal (hide pht.repr.seq)) (SZ.v idx) (mk_used_cell k v)))
                   as (V.pts_to ht.contents (insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq);
              cont := false;
              fold (exploded_vp r ht res);
            }
            Zombie ->
            {
              fold (models ht pht);
              fold (exploded_vp r ht res);
              let lookup_res = pulse_lookup_index r res k;
              unfold (models ht pht);
              unfold (exploded_vp r ht res);

              if (fst lookup_res)
              {
                let o = snd lookup_res;
                match o
                {
                  Some p ->
                  {
                    rewrite (V.pts_to ht.contents pht.repr.seq)
                         as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
                    vec_ref_write (tthd res) (snd p) Zombie;
                    vec_ref_write (tthd res) idx (mk_used_cell k v);
                    cont := false;
                    assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal` 
                                  Seq.upd (Seq.upd pht.repr.seq (SZ.v (snd p)) Zombie) (SZ.v idx) (mk_used_cell k v)));
                    rewrite (V.pts_to (reveal (hide ht.contents))
                                      (Seq.upd (Seq.upd (reveal (hide pht.repr.seq)) (SZ.v (snd p)) Zombie) (SZ.v idx) (mk_used_cell k v)))
                         as (V.pts_to ht.contents (insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq);
                    fold (exploded_vp r ht res);
                  }
                  None ->
                  {
                    rewrite (V.pts_to ht.contents pht.repr.seq)
                         as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
                    vec_ref_write (tthd res) idx (mk_used_cell k v);                    
                    cont := false;
                    assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal`
                                  Seq.upd pht.repr.seq (SZ.v idx) (mk_used_cell k v)));
                    rewrite (V.pts_to (reveal (hide ht.contents)) (Seq.upd (reveal (hide pht.repr.seq)) (SZ.v idx) (mk_used_cell k v)))
                         as (V.pts_to ht.contents (insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq);
                    fold (exploded_vp r ht res);
                  }
                }
              }
              else
              {
                // ERROR - lookup failed
                err := true;
                fold (exploded_vp r ht res);
              }
            }
          }
        }
        None ->
        {
          // ERROR - add failed
          err := true;
          fold (exploded_vp r ht res);
        }
      }
    }
  };
  unexplode_ref r res;
  let verr = !err;
  if verr
  {
    fold (models ht pht);
    false
  } else {
    assert (V.pts_to ht.contents (PHT.insert pht k v).repr.seq);
    fold (models ht (PHT.insert pht k v));
    true
  }
}
```

```pulse
fn delete (#kt:eqtype) (#vt:Type0)
  (r:ref (ht_t kt vt)) (k:kt)
  (#ht:erased (ht_t kt vt))
  (#pht:erased (pht_t kt vt))
  requires pts_to r ht ** models ht pht
  returns b:bool
  ensures exists ht' pht'.
    pts_to r ht' **
    models ht' pht' **
    pure (if b then pht' == PHT.delete pht k else pht' == pht)
{
  let res = explode_ref r;

  unfold (exploded_vp r ht res);
  let sz = !(tfst res);
  let hash = ref_apply (tsnd res) k;
  fold (exploded_vp r ht res);

  let cidx = size_t_mod hash sz;
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
    exploded_vp r ht res **
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    V.pts_to ht.contents (if (vcont || verr) then pht.repr.seq else (PHT.delete pht k).repr.seq) **
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
    unfold (exploded_vp r ht res);
    let voff = !off;
    if (voff = sz)
    {
      cont := false;
      assert (V.pts_to ht.contents pht.repr.seq);
      fold (exploded_vp r ht res);
    }
    else
    {
      let opt_sum = cidx `sz_add` voff;
      match opt_sum
      {
        Some sum ->
        {
          let idx = size_t_mod sum sz;
          rewrite (V.pts_to ht.contents pht.repr.seq)
               as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
          let c = vec_ref_read (tthd res) idx;
          rewrite (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)))
               as (V.pts_to ht.contents pht.repr.seq);

          match c
          {
            Used k' v' ->
            { 
              if (k' = k)
              {
                rewrite (V.pts_to ht.contents pht.repr.seq)
                     as (V.pts_to (reveal (hide ht.contents)) (reveal (hide pht.repr.seq)));
                vec_ref_write (tthd res) idx Zombie;
                cont := false;
                assert (pure (pht.repr @@ SZ.v idx == Used k v'));
                assert (pure (Seq.upd pht.repr.seq (SZ.v idx) Zombie  `Seq.equal`
                              (PHT.delete pht k).repr.seq));
                rewrite (V.pts_to (reveal (hide ht.contents)) (Seq.upd (reveal (hide pht.repr.seq)) (SZ.v idx) Zombie))
                     as (V.pts_to ht.contents (PHT.delete pht k).repr.seq);
                fold (exploded_vp r ht res);
              }
              else
              {
                off := SZ.(voff +^ 1sz);
                fold (exploded_vp r ht res);
              } 
            }
            Clean ->
            {
              cont := false;
              assert (pure (pht.repr == (PHT.delete pht k).repr));
              fold (exploded_vp r ht res);
            }
            Zombie ->
            {
              off := SZ.(voff +^ 1sz);
              fold (exploded_vp r ht res);
            }
          }
        }
        None ->
        {
          // ERROR - add failed
          err := false;
          fold (exploded_vp r ht res);
        }
      }
    }
  };
  unexplode_ref r res;
}
```

```pulse
fn not_full' (#kt:eqtype) (#vt:Type0)
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
      let c = V.op_Array_Access ht.contents vi; 
      (Used? c) 
    }
    else 
    { 
      false
    }
  )
  invariant b. exists (vi:SZ.t). (
    V.pts_to ht.contents pht.repr.seq **
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
fn test_mono' ()
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
