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

let models (s:pht_sig_us) (ht:ht_t s) (pht:pht_t (s_to_ps s)) : vprop
= A.pts_to ht.contents pht.repr **
  pure (
    SZ.v ht.sz == pht.sz /\
    A.is_full_array ht.contents
  )

```pulse
fn alloc' (#s:pht_sig_us) (l:pos_us)
  requires emp
  returns ht:ht_t s
  ensures exists pht. models s ht pht
{
  let contents = A.alloc #(cell s.keyt s.valt) Clean l;
  let ht = mk_ht l contents;
  let pht = Ghost.hide (mk_init_pht #s l);
  rewrite (A.pts_to contents (Seq.create (SZ.v l) Clean))
    as (A.pts_to ht.contents pht.repr);
  fold (models s ht pht);
  ht
}
```
let alloc = alloc'

let perform (#a:Type0) (#b:Type0) (f:  (a -> stt b emp (fun _ -> emp))) (x:a) 
  : stt b emp (fun _ -> emp)
  = f x

```pulse
fn dealloc' (#s:pht_sig_us) (ht:ht_t s) (l:pos_us) 
  (destroy_val:destroy_fn_t s.valt)
  (destroy_key:destroy_fn_t s.keyt)
  requires exists pht. models s ht pht
  ensures emp
{
  open SZ;
  let mut off = 0sz;

  with pht. assert (models s ht pht);
  unfold (models s ht pht);

  while (let voff = !off; (voff <^ ht.sz))
  invariant b. exists (voff:SZ.t). (
    A.pts_to ht.contents pht.repr **
    R.pts_to off voff **
    pure (
      SZ.v ht.sz == pht.sz /\
      voff <=^ ht.sz /\
      b == (voff <^ ht.sz)
    )
  )
  {
    let voff = !off;
    let c = ht.contents.(voff);
    match c
    {
      Used k v ->
      {
        perform destroy_val v;
        perform destroy_key k;
      }
      _ ->
      {
        off := voff +^ 1sz;
      }
    }
  };
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

#push-options "--z3rlimit_factor 4 --query_stats"
```pulse
fn pulse_lookup_index (#s:pht_sig_us)
                      (#pht:erased (pht_t (s_to_ps s)))
                      (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  returns  p:bool & option (s.valt & SZ.t)
  ensures  models s ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup_index_us pht k )
{
  open SZ;
  let cidx = s.hashf k %^ ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;
  let mut ret = None #(s.valt & SZ.t);
  unfold (models s ht pht);
  while (let voff = !off;
         let vcont = !cont;
         let verr = !err; 
         (voff <=^ ht.sz && vcont = true && verr = false)) 
  invariant b. exists (voff:SZ.t) (vcont verr:bool). (
    A.pts_to ht.contents pht.repr **
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    R.pts_to ret (if (vcont || verr) then None else (PHT.lookup_index_us pht k)) **
    pure (
      SZ.v ht.sz == pht_sz pht /\
      voff <=^ ht.sz /\
      walk_get_idx #(s_to_ps s) #(pht_sz pht) pht.repr (SZ.v cidx) k (SZ.v voff) 
        == lookup_repr_index #(s_to_ps s) #(pht_sz pht) pht.repr k /\
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
          let idx = sum %^ ht.sz;
          let c = ht.contents.(idx); 
          match c
          {
            Used k' v' ->
            {
              if (k' = k)
              {
                cont := false;
                ret := Some (v', idx); //(op_Colon_Equals ret (Some (v',idx)) #None);
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
  fold (models s ht pht);
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
fn lookup' (#s:pht_sig_us)
           (#pht:erased (pht_t (s_to_ps s)))
           (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  returns  p:bool & option s.valt
  ensures  models s ht pht ** 
           pure ( fst p ==> (snd p) == PHT.lookup pht k )
{
  let p = pulse_lookup_index #s #pht ht k;
  if (fst p)
  {
    match (snd p)
    {
      Some p -> { (true, Some (fst p)) }
      None -> { (true, None #s.valt) }
    }
  } 
  else
  {
    (false, None #s.valt)
  }
}
```
let lookup = lookup'

#push-options "--z3rlimit_factor 8 --query_stats"
open Pulse.Lib.BoundedIntegers

```pulse
fn insert' (#s:pht_sig_us)
           (#pht:(p:erased (pht_t (s_to_ps s)){PHT.not_full p.repr}))
           (ht:ht_t s) (k:s.keyt) (v:s.valt)
  requires models s ht pht
  returns b:bool
  ensures maybe_update b s ht pht (PHT.insert pht k v)
{
  let cidx = s.hashf k % ht.sz;
  // match opt_cidx {
  // Some cidx -> {
  assert (pure (SZ.v cidx == SZ.v (s.hashf k) % SZ.v ht.sz));
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;

  unfold (models s ht pht);

  while (let voff = !off; let vcont = !cont; let verr = !err; (voff <= ht.sz && vcont = true && verr = false)) 
  invariant b. exists (voff:SZ.t) (vcont verr:bool). (
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    A.pts_to ht.contents (if (vcont || verr) then pht.repr else (PHT.insert pht k v).repr) **
    pure (
      SZ.v ht.sz == pht_sz pht /\
      voff <= ht.sz /\
      strong_all_used_not_by pht.repr (SZ.v cidx) (SZ.v voff) k /\
      walk pht.repr (SZ.v cidx) k (SZ.v voff) == lookup_repr pht.repr k /\
      insert_repr_walk #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v (SZ.v voff) (SZ.v cidx) () () 
        == insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v /\
      b == (voff <= ht.sz && vcont = true && verr = false)
    ))
  {
    let voff = !off;
    if (voff = ht.sz) {
      cont := false;
      assert (A.pts_to ht.contents pht.repr);
    } else {
      let opt_sum = cidx `safe_add` voff;
      match opt_sum {
      Some sum -> {
        let idx = sum % ht.sz;
        let c = (ht.contents).(idx); 
        match c {
        Used k' v' -> { 
          if (k' = k) {
            assert (A.pts_to ht.contents pht.repr);
            assert (pure ( SZ.v idx < Seq.length pht.repr));
            ((ht.contents).(idx) <- (mk_used_cell k v));
            cont := false;
            assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
                          Seq.upd pht.repr (SZ.v idx) (mk_used_cell k v))); 
          } else {
            off := voff + 1sz;
          } 
        }
        Clean -> {
          ((ht.contents).(idx) <- (mk_used_cell k v));
          cont := false;
          assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
                  Seq.upd pht.repr (SZ.v idx) (mk_used_cell k v)));
        }
        Zombie -> {
          fold (models s ht pht);
          let res = pulse_lookup_index #s #pht ht k;
          unfold (models s ht pht);
          if (fst res) {
            let o = snd res;
            match o {
              Some p -> {
                ((ht.contents).(snd p) <- Zombie);
                ((ht.contents).(idx) <- (mk_used_cell k v));
                cont := false;
                assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal` 
                              Seq.upd (Seq.upd pht.repr (SZ.v (snd p)) Zombie) (SZ.v idx) (mk_used_cell k v)));
              }
              None -> { 
                ((ht.contents).(idx) <- (mk_used_cell k v)); 
                cont := false;
                assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k v `Seq.equal`
                              Seq.upd pht.repr (SZ.v idx) (mk_used_cell k v)));
              }
          }} else {
            // ERROR - lookup failed
            err := true;
          }
        }
      }
    }
    None -> {
      // ERROR - add failed
      err := true 
    }}}
  };
  let verr = !err;
  if verr {
    fold (models s ht pht);
    fold (maybe_update false s ht pht (PHT.insert pht k v));
    false
  } else {
    fold (models s ht (PHT.insert pht k v));
    fold (maybe_update true s ht pht (PHT.insert pht k v));
    true
  }
  // }

  // None -> {
  //   fold (maybe_update false s ht pht (PHT.insert pht k v));
  //   false
  // }}
}
```

// ```pulse
// fn insert' (#s:pht_sig_us)
//            (#pht:(p:erased (pht_t (s_to_ps s)){PHT.not_full p.repr}))
//            (ht:ht_t s) (k:s.keyt) (value:s.valt)
//   requires models s ht pht
//   returns b:bool
//   ensures maybe_update b s ht pht (PHT.insert pht k value)
// {
//   // open SZ;
//   let cidx = SZ.(s.hashf k %^ ht.sz);
//   assert (pure (SZ.v cidx == SZ.v (s.hashf k) % SZ.v ht.sz));
//   let mut off = 0sz;
//   let mut cont = true;
//   let mut err = false;

//   unfold (models s ht pht);

//   while (let voff = !off;
//          let vcont = !cont;
//          let verr = !err; 
//          (SZ.(voff <=^ ht.sz) && vcont = true && verr = false)) 
//   invariant b. exists (voff:SZ.t) (vcont verr:bool). (
//     R.pts_to off voff **
//     R.pts_to cont vcont **
//     R.pts_to err verr **
//     A.pts_to ht.contents (if (vcont || verr) then pht.repr else (PHT.insert pht k value).repr) **
//     pure (
//       SZ.v ht.sz == pht_sz pht /\
//       SZ.(voff <=^ ht.sz) /\
//       strong_all_used_not_by pht.repr (SZ.v cidx) (SZ.v voff) k /\
//       walk pht.repr (SZ.v cidx) k (SZ.v voff) == lookup_repr pht.repr k /\
//       insert_repr_walk #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k value (SZ.v voff) (SZ.v cidx) () () 
//         == insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k value /\
//       b == (SZ.(voff <=^ ht.sz) && vcont = true && verr = false)
//     ))
//   {
//     let voff = !off;
//     if (voff = ht.sz)
//     {
//       cont := false;
//       assert (A.pts_to ht.contents pht.repr);
//     }
//     else
//     {
//       let opt_sum = cidx `sz_add` voff;
//       match opt_sum
//       {
//         Some sum ->
//         {
//           let idx = SZ.(sum %^ ht.sz);
//           let c = ht.contents.(idx); 
//           match c
//           {
//             Used k' v' ->
//             { 
//                admit()
//       //         if (k' = k)
//       //         {
//       //           assert (A.pts_to ht.contents pht.repr);
//       //           assert (pure ( SZ.v idx < Seq.length pht.repr));
//       //           ht.contents.(idx) <- (mk_used_cell k value);
//       //           cont := false;
//       //           assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k value `Seq.equal` 
//       //                         Seq.upd pht.repr (SZ.v idx) (mk_used_cell k value))); 
//       //         }
//       //         else
//       //         {
//       //           off := SZ.(voff +^ 1sz);
//       //         } 
//             }
//             Clean ->
//             {
//               ht.contents.(idx) <- (mk_used_cell k value);
//               cont := false;
//               assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k value `Seq.equal` 
//                       Seq.upd pht.repr (SZ.v idx) (mk_used_cell k value)));
//             }
//             Zombie ->
//             {
//                  admit()
//       //         fold (models s ht pht);
//       //         let res = pulse_lookup_index #s #pht ht k;
//       //         unfold (models s ht pht);
//       //         if (fst res)
//       //         {
//       //           let o = snd res;
//       //           match o
//       //           {
//       //             Some p ->
//       //             {
//       //               ht.contents.(snd p) <- Zombie;
//       //               ht.contents.(idx) <- (mk_used_cell k value);
//       //               cont := false;
//       //               assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k value `Seq.equal` 
//       //                             Seq.upd (Seq.upd pht.repr (SZ.v (snd p)) Zombie) (SZ.v idx) (mk_used_cell k value)));
//       //             }
//       //             None ->
//       //             { 
//       //               ht.contents.(idx) <- (mk_used_cell k value); 
//       //               cont := false;
//       //               assert (pure (insert_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k value `Seq.equal`
//       //                             Seq.upd pht.repr (SZ.v idx) (mk_used_cell k value)));
//       //             }
//       //           }
//       //         } 
//       //         else
//       //         {
//       //           // ERROR - lookup failed
//       //           err := true;
//       //         }
//             }
//           }
//         }
//         None ->
//         {
//           // ERROR - add failed
//           err := true 
//         }
//       }
//     }
//   };
//   let verr = !err;
//   if verr
//   {
//     fold (models s ht pht);
//     fold (maybe_update false s ht pht (PHT.insert pht k value));
//     false
//   }
//   else
//   {
//     fold (models s ht (PHT.insert pht k value));
//     fold (maybe_update true s ht pht (PHT.insert pht k value));
//     true
//   }
// }
// ```
#pop-options

let insert = insert'

#push-options "--z3rlimit_factor 4 --query_stats"
#restart-solver

```pulse
fn delete' (#s:pht_sig_us)
           (#pht:erased (pht_t (s_to_ps s)))
           (ht:ht_t s) (k:s.keyt)
  requires models s ht pht
  returns b:bool
  ensures maybe_update b s ht pht (PHT.delete pht k)
{
  let cidx = s.hashf k % ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;

  unfold (models s ht pht);
  while (let voff = !off;
         let vcont = !cont;
         let verr = !err; 
         (voff <= ht.sz && vcont = true && verr = false))
  invariant b. exists (voff:SZ.t) (vcont verr:bool). (
    R.pts_to off voff **
    R.pts_to cont vcont **
    R.pts_to err verr **
    A.pts_to ht.contents (if (vcont || verr) then pht.repr else (PHT.delete pht k).repr) **
    pure (
      SZ.v ht.sz == pht_sz pht /\
      voff <= ht.sz /\
      all_used_not_by pht.repr (SZ.v cidx) (SZ.v voff) k /\
      walk pht.repr (SZ.v cidx) k (SZ.v voff) == lookup_repr pht.repr k /\
      delete_repr_walk #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k (SZ.v voff) (SZ.v cidx) () () 
        == delete_repr #(s_to_ps s) #(pht_sz pht) #pht.spec pht.repr k /\
      b == (voff <= ht.sz && vcont = true && verr = false)
    ))
  {
    let voff = !off;
    if (voff = ht.sz)
    {
      cont := false;
      assert (A.pts_to ht.contents pht.repr);
    }
    else
    {
      let opt_sum = cidx `safe_add` voff;
      match opt_sum
      {
        Some sum ->
        {
          let idx = sum % ht.sz;
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
                assert (pure (Seq.upd pht.repr (SZ.v idx) Zombie 
                  `Seq.equal` (PHT.delete pht k).repr));
              }
              else
              {
                off := voff + 1sz;
              } 
            }
            Clean ->
            {
              cont := false;
              assert (pure (pht.repr == (PHT.delete pht k).repr));
            }
            Zombie ->
            {
              off := voff + 1sz;
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
    fold (models s ht pht);
    fold (maybe_update false s ht pht (PHT.delete pht k));
    false
  }
  else
  {
    fold (models s ht (PHT.delete pht k));
    fold (maybe_update true s ht pht (PHT.delete pht k));
    true
  }
}
```
let delete = delete'


```pulse
fn not_full' (#s:pht_sig_us) (#pht:erased (pht_t (s_to_ps s))) (ht:ht_t s)
  requires models s ht pht
  returns b:bool
  ensures models s ht pht ** 
          pure (b ==> PHT.not_full #(s_to_ps s) #(pht_sz pht) pht.repr)
{
  let mut i = 0sz;
  unfold (models s ht pht);

  while
  (
    let vi = !i;  
    if (vi < ht.sz) 
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
    A.pts_to ht.contents pht.repr **
    R.pts_to i vi **
    pure (
      SZ.v ht.sz == pht_sz pht /\
      vi <= ht.sz /\
      (b == (vi < ht.sz && Used? (pht.repr @@ (SZ.v vi)))) /\
      (forall (i:nat). i < SZ.v vi ==> Used? (pht.repr @@ i))
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
let not_full = not_full'
