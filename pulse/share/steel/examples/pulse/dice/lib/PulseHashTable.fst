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


#set-options "--split_queries no"

let insert_loop_inv_def (#s:pht_sig) (b:bool)
  (pht:(p:pht s{not_full p.repr}))
  (ht:ht s)
  (off: R.ref nat) (cont: R.ref bool)
  (k:s.keyt) (v:s.valt)
  (voff:nat) (vcont:bool)
=
  // `@(if vcont=true 
  //   then (A.pts_to ht.contents full_perm pht.repr) 
  //   else (A.pts_to ht.contents full_perm (PHT.insert pht k v).repr)) `star`
  R.pts_to off full_perm voff `star`
  R.pts_to cont full_perm vcont `star`
  models s (if vcont then pht else PHT.insert pht k v) ht `star`
  pure (
    voff >= 0 /\ voff <= ht.sz /\
    // walk_ pht.repr cidx k off == PHT.insert pht k v /\
    // walk pht.repr cidx k off == lookup_repr pht.repr k /\
    // strong_all_used_not_by #s #sz pht.repr cidx voff k /\
    b == (voff <= ht.sz && vcont = true))

let insert_loop_inv (#s:pht_sig) (b:bool)
  (pht:(p:pht s{not_full p.repr}))
  (ht:ht s)
  (off: R.ref nat) (cont: R.ref bool)
  (k:s.keyt) (v:s.valt)
=
  exists_ (fun (voff:nat) ->
    exists_ (fun (vcont:bool) ->
      insert_loop_inv_def b pht ht off cont k v voff vcont))

// [@@expect_failure]
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

  // assume_ (exists_ (fun b -> insert_loop_inv b pht ht off cont k v));
  // with b.
  //   assert (insert_loop_inv b pht ht off cont k v);
  // introduce
  //   exists (b:bool). insert_loop_inv b pht ht off cont k v
  //   with (0 <= ht.sz && = true);

  // rewrite (models s pht ht)
  //       as (models s (match true with | true -> pht | _ -> PHT.insert pht k v) ht);
  // fold (insert_loop_inv_def true pht ht off cont k v 0 true);
  // rewrite (insert_loop_inv_def true pht ht off cont k v 0 true)
  //      as (insert_loop_inv_def true pht ht off cont k v (reveal (hide 0)) (reveal (hide true)));
  // introduce exists (voff:nat) (vcont:bool).
  //             insert_loop_inv_def true pht ht off cont k v (reveal voff) (reveal vcont)
  //      with 0 true;
  // assert emp;
  // with (voff:Ghost.erased nat) (vcont:Ghost.erased bool).
  //   assert (insert_loop_inv_def true pht ht off cont k v (Ghost.reveal voff) (Ghost.reveal vcont));

  // assert (insert_loop_inv_def true pht ht off cont k v (Ghost.reveal voff) (Ghost.reveal vcont));
  // rewrite (insert_loop_inv_def true pht ht off cont k v (Ghost.reveal voff) (Ghost.reveal vcont))
  //      as (insert_loop_inv_def true pht ht off cont k v
  //           (reveal (hide (reveal (hide (reveal voff)))))
  //           (reveal (hide (reveal (hide (reveal vcont))))));

  // rewrite (insert_loop_inv_def true pht ht off cont k v (reveal (hide voff)) (reveal (hide vcont)))
  //      as (insert_loop_inv_def true pht ht off cont k v (reveal (hide voff)) (reveal (hide vcont)))
  //fold (insert_loop_inv true pht ht off cont k v);
    

  // rewrite (exists (voff:nat) (vcont:bool).
  //             insert_loop_inv_def true pht ht off cont k v (reveal voff) (reveal vcont))
  //      as (insert_loop_inv true pht ht off cont k v);
  assume_ (insert_loop_inv true pht ht off cont k v);

  assert emp;

  let zz = 42;
  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. insert_loop_inv b pht ht off cont k v
  {
    assume_ (exists_ (fun b -> insert_loop_inv b pht ht off cont k v));
    // if (off=sz) {
    // admit()
    // } else {
      (*
    let voff = !off;
    let idx = coerce_us ((cidx+voff)%sz);
    assume_ (pure (US.v idx < pht.sz)); // FIXME: can prove based on modulo calc above
    let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
    match c {
      Used k' v' -> { 
        if (k' = k) {
          op_Array_Assignment ht.contents idx (mk_used_cell k v);
          cont := false;
          ()
        } else {
          off := voff + 1;
          ()
        } 
      }
      Clean -> {
        op_Array_Assignment ht.contents idx (mk_used_cell k v);
        cont := false;
        ()
      }
      Zombie -> {
        let o = lookup ht k;
        match o {
          Some p -> {
            op_Array_Assignment ht.contents (snd p) Zombie;
            op_Array_Assignment ht.contents idx (mk_used_cell k v);
          }
          None -> { op_Array_Assignment ht.contents idx (mk_used_cell k v); }
        };
        cont := false;
        ()
      }
      *)
      ()
    //};
    };
    fold (models s (PHT.insert pht k v) ht);
    ()
}
```


[@@expect_failure]
```pulse
fn delete (#s:pht_sig) (#pht:pht s) 
          (ht:ht s) (k:s.keyt)
  requires models s pht ht
  ensures  models s (PHT.delete pht k) ht
{
  let sz = ht.sz;
  let a = ht.contents;
  let cidx = canonical_index k sz;
  let mut off = 0;

  while (let voff = !off; let vcont = !cont; (voff <= sz && vcont = true))
  invariant b. insert_loop_inv b pht ht off cont k v // FIXME: delete loop invar
  {
    if (off=sz) {
    ()
    } else {
    let voff = !off;
    let idx = coerce_us ((cidx+voff)%sz);
    assume_ (pure (US.v idx < pht.sz)); // FIXME: can prove based on modulo calc above
    let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
    match c {
      Used k' v' -> { 
        if (k' = k) {
          op_Array_Assignment ht.contents idx Zombie;
          cont := false;
          ()
        } else {
          off := voff + 1;
          ()
        } 
      }
      Clean -> {
        cont := false;
        ()
      }
      Zombie -> { 
        off := voff + 1;
        () 
      }
    };};}
    fold (models s (PHT.delete pht k) ht);
    ()
}
```


[@@expect_failure]
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
  invariant b. exists (voff:nat) (vcont:bool) (o:option s.valt). (
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to off full_perm voff **
    R.pts_to cont full_perm vcont **
    R.pts_to ret full_perm o **
    pure (
      (if vcont=true
        then o == None 
        else o == PHT.lookup pht k) /\
      b == (voff <= sz && vcont = true)
    )
  )
  {
    let voff = !off;
    if (voff = sz) {
      cont := false;
      ()
    } else {
      let idx = coerce_us ((cidx+voff)%sz);
      assume_ (pure (US.v idx < pht.sz)); // FIXME: can prove based on modulo calc above
      let c = op_Array_Index ht.contents #full_perm #pht.repr idx;
      match c {
        Used k' v' -> { 
          if (k' = k) {
            cont := false;
            ret := Some v';
            ()
          } else {
            off := voff + 1;
            () 
          }}
        Clean -> { 
          cont := false;
          ()
         }
        Zombie -> { 
          off := voff + 1;
          () 
         }
      };
    };
  };
  fold (models s pht ht);
  ret
}
```
