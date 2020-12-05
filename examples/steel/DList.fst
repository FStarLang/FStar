module DList
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
open DList.Invariant
open Utils


//We're trying to write this library in the "internal" language of Steel
//the front end + frame inference should elaborate into something like this
//If it does, then the proofs can be done with almost nothing in the SMT context
//except very basic stuff from Prims and Pervasives
//and application-specific stuff for this particular module (Steel.DList)
let new_dlist (#a:Type) (init:a)
  : Steel (t a & cell a)
          emp
          (fun pc -> dlist null_dlist (fst pc) null_dlist [snd pc])
          (requires fun _ -> True)
    (ensures fun _ pc _ ->
      data (snd pc) == init)
  = let cell = mk_cell null_dlist null_dlist init in
    let p = alloc cell in
    assume (p =!= null_dlist);
    intro_dlist_nil p null_dlist;
    change_slprop (dlist p null_dlist null_dlist [])
                  (dlist p (next cell) null_dlist [])
                  (fun _ -> ());
    intro_dlist_cons null_dlist p null_dlist cell [];
    let pc = p, cell in
    pc

let read_head (#a:_) (from0:t a) (ptr0:t a) (to0: t a)
              (hd:cell a)
              (tl:list (cell a))
  : Steel (cell a)
    (dlist from0 ptr0 to0 (hd::tl))
    (fun v -> dlist from0 ptr0 to0 (v::tl))
    (requires fun _ ->
      True)
    (ensures fun _ v _ ->
      v == hd)
  =  //1: unfold dlist to dlist cons
     elim_dlist_cons from0 ptr0 to0 hd tl;

     //2: read the ptr0 to get cell0
     let c0 = read ptr0 in

     change_slprop (dlist ptr0 (next hd) to0 tl)
                   (dlist ptr0 (next c0) to0 tl)
                   (fun _ -> ());

     //3: fold it back into a dlist
     intro_dlist_cons from0 ptr0 to0 c0 tl;

     c0

let set_prev (c:cell 'a) (prev: t 'a)
  : Tot (cell 'a)
  = mk_cell prev (next c) (data c)

let set_next (c:cell 'a) (next: t 'a)
  : Tot (cell 'a)
  = mk_cell (prev c) next (data c)

let intro_dlist_cons (#a:Type) (left:t a)
                               (ptr:t a)
                               (right:t a)
                               (hd: cell a)
                               (ptr1 : t a)
                               (tl: list (cell a))
   : Steel unit
     (pts_to ptr full_perm hd `star` dlist ptr ptr1 right tl)
     (fun _ -> dlist left ptr right (hd::tl))
     (requires fun _ ->
       prev hd == left /\
       next hd == ptr1 /\
       ptr =!= right)
     (ensures fun _ _ _ -> True)
   = change_slprop (dlist ptr ptr1 right tl)
                   (dlist ptr (next hd) right tl)
                   (fun _ -> ());
     intro_dlist_cons left ptr right hd tl

let write_prev (#a:_) (#from0:t a) (ptr0:t a) (#to0: t a)
               (#hd:cell a)
               (#tl:list (cell a))
               (prev:t a)
    : SteelT unit
      (dlist from0 ptr0 to0 (hd::tl))
      (fun _ -> dlist prev ptr0 to0  (set_prev hd prev :: tl))
    = elim_dlist_cons _ ptr0 _ _ _;
      write ptr0 (set_prev hd prev);
      intro_dlist_cons _ ptr0 _ _ _ _

let concat_nil_l (#a:Type)
                 (from0:t a) (ptr0:t a) (to0: t a) (hd:cell a) (tl0:list (cell a))
                 (from1:t a) (ptr1:t a) (hd1:cell a) (tl1:list (cell a))
   : Steel (list (cell a))
     (pts_to ptr0 full_perm hd `star`
      dlist ptr0 to0 to0 tl0 `star`
      dlist from1 ptr1 null_dlist (hd1::tl1))
     (fun l -> dlist from0 ptr0 null_dlist l)
     (requires fun _ ->
       prev hd == from0 /\
       to0 =!= ptr0)
     (ensures fun _ _ _ -> True)
   = assume (ptr0 =!= null_dlist);

     // 1. invert dlist tl0 to dlist []
     invert_dlist_nil_eq ptr0 to0 to0 tl0;
     drop (dlist ptr0 to0 to0 []);
     // tl0 == []

     // 2. ptr0.next <- ptr1
     write ptr0 (set_next hd ptr1);

     write_prev ptr1 ptr0;

     intro_dlist_cons from0 ptr0 _ _ ptr1 _;

     drop (pure (tl0 == []));
     (set_next hd ptr1
             :: set_prev hd1 ptr0
             :: tl1)

let concat_t a =
  (#[@@framing_implicit] from0:t a) ->
  (#[@@framing_implicit] to0: t a) ->
  (#[@@framing_implicit] hd0:cell a) ->
  (#[@@framing_implicit] tl0:list (cell a)) ->
  (#[@@framing_implicit] from1:t a) ->
  (#[@@framing_implicit] hd1:cell a) ->
  (#[@@framing_implicit] tl1:list (cell a)) ->
  (ptr0:t a) ->
  (ptr1:t a) ->
  SteelT (list (cell a))
     (dlist from0 ptr0 to0 (hd0::tl0) `star`
      dlist from1 ptr1 null_dlist (hd1::tl1))
     (fun l ->
       dlist from0 ptr0 null_dlist l)

let concat_cons (#a:Type) (aux:concat_t a)
                (from0:t a) (ptr0:t a) (to0: t a) (c0:cell a) (tl0:list (cell a))
                (from1:t a) (ptr1:t a) (hd1:cell a) (tl1:list (cell a))
   : Steel (list (cell a))
     (pts_to ptr0 full_perm c0 `star`
      dlist ptr0 (next c0) to0 tl0 `star`
      dlist from1 ptr1 null_dlist (hd1::tl1))
     (fun l -> dlist from0 ptr0 null_dlist l)
     (requires fun _ ->
       next c0 =!= to0 /\
       prev c0 == from0)
     (ensures fun _ _ _ -> True)
   = invert_dlist_cons_neq ptr0 (next c0) to0 tl0;
     let Cons hd0 tl0' = tl0 in
     change_slprop (dlist ptr0 (next c0) to0 tl0)
                   (dlist ptr0 (next c0) to0 (hd0::tl0'))
                   (fun _ -> ());
     let l = aux (next c0) ptr1 in
     assume (ptr0 =!= null_dlist);
     intro_dlist_cons from0 ptr0 _ _ (next c0) _;
     c0::l

let rec concat (#a:Type)
               (#[@@framing_implicit] from0:t a)
               (#[@@framing_implicit] to0: t a)
               (#[@@framing_implicit] hd0:cell a)
               (#[@@framing_implicit] tl0:list (cell a))
               (#[@@framing_implicit] from1:t a)
               (#[@@framing_implicit] hd1:cell a)
               (#[@@framing_implicit] tl1:list (cell a))
               (ptr0:t a)
               (ptr1:t a)
   : SteelT (list (cell a))
     (dlist from0 ptr0 to0 (hd0::tl0) `star`
      dlist from1 ptr1 null_dlist (hd1::tl1))
     (fun l ->
       dlist from0 ptr0 null_dlist l)
   =
     let to1 = null_dlist #a in

     //1: read the ptr0 to get cell0

     let c0 = read_head from0 ptr0 to0 hd0 tl0 in

     //2: unfold dlist to dlist cons
     elim_dlist_cons from0 ptr0 to0 c0 tl0;

     let b = ptr_eq (next c0) to0 in

     change_slprop
        (pts_to ptr0 full_perm c0 `star`
         dlist ptr0 (next c0) to0 tl0 `star`
         dlist from1 ptr1 null_dlist (hd1::tl1))
        (pts_to ptr0 full_perm c0 `star`
         (if b
          then dlist ptr0 to0 to0 tl0
          else dlist ptr0 (next c0) to0 tl0) `star`
         dlist from1 ptr1 null_dlist (hd1::tl1))
        (fun _ -> ());
     cond b
       (fun b' ->
         pts_to ptr0 full_perm c0 `star`
         (if b'
          then dlist ptr0 to0 to0 tl0
          else dlist ptr0 (next c0) to0 tl0) `star`
          dlist from1 ptr1 null_dlist (hd1::tl1))
       (fun b l -> dlist from0 ptr0 null_dlist l)
       (fun _ ->
         concat_nil_l from0 ptr0 to0 c0 tl0
                      from1 ptr1 hd1 tl1)
       (fun _ ->
         concat_cons (concat #a)
                     from0 ptr0 to0 c0 tl0
                     from1 ptr1 hd1 tl1)

let snoc (#a:Type)
         (#[@@framing_implicit] from0:t a)
         (#[@@framing_implicit] to0: t a)
         (#[@@framing_implicit] hd0:cell a)
         (#[@@framing_implicit] l0:list (cell a))
         (ptr0:t a)
         (v:a)
   : SteelT (list (cell a))
     (requires
       dlist from0 ptr0 to0 (hd0::l0))
     (ensures
       dlist from0 ptr0 null_dlist)
     // (requires fun _ ->
     //   Cons? l0)
     // (ensures fun _ l _ ->
     //   datas l == datas l0 @ datas [mk_cell null_dlist null_dlist v])
   = let tl = new_dlist v in
     concat #_ #_ #_ #_ #_ #null_dlist #(snd tl) #[] ptr0 (fst tl)

let cons (#a:Type)
         (from0:t a) (ptr0:t a) (hd0:cell a) (l0:list (cell a))
         (v:a)
   : SteelT (t a & list (cell a))
     (requires
       dlist from0 ptr0 null_dlist (hd0::l0))
     (ensures fun pc ->
       dlist null_dlist (fst pc) null_dlist (snd pc))
     // (requires fun _ ->
     //   Cons? l0)
     // (ensures fun _ pc _ ->
     //   datas (snd pc) == datas [mk_cell null_dlist null_dlist v] @ datas l0)
   = let pc = new_dlist v in
     let l = concat #_ #null_dlist #null_dlist #(snd pc) #[] (fst pc) ptr0 in
     fst pc, l


let returnF (#a:_)
            (q:(a -> slprop))
            (x:a)
    : SteelF a (q x) q (fun _ -> True) (fun _ _ _ -> True)
    = sladmit_depF ()

(* this version of concat tries to use if/then/else
   instead of a cond combinator ...
   and seems like with some work it could actually work *)
let rec concat_alt (#a:Type)
               (#[@@framing_implicit] from0:t a)
               (#[@@framing_implicit] to0: t a)
               (#[@@framing_implicit] hd0:cell a)
               (#[@@framing_implicit] tl0:list (cell a))
               (#[@@framing_implicit] from1:t a)
               (#[@@framing_implicit] hd1:cell a)
               (#[@@framing_implicit] tl1:list (cell a))
               (ptr0:t a)
               (ptr1:t a)
   : SteelT (list (cell a))
     (dlist from0 ptr0 to0 (hd0::tl0) `star`
      dlist from1 ptr1 null_dlist (hd1::tl1))
     (fun l ->
       dlist from0 ptr0 null_dlist l)
   =
     let to1 = null_dlist #a in

     //1: read the ptr0 to get cell0

     let c0 = read_head from0 ptr0 to0 hd0 tl0 in

     //2: unfold dlist to dlist cons
     elim_dlist_cons from0 ptr0 to0 c0 tl0;

     let b = ptr_eq (next c0) to0 in

     if b
     then (
       (* refine just a small part of the context assertion based on b *)
       change_slprop
         (dlist ptr0 (next c0) to0 tl0)
         (dlist ptr0 to0 to0 tl0)
         (fun _ -> ());

       (* inline concat_nil_l *)
       // 1. invert dlist tl0 to dlist []
       invert_dlist_nil_eq ptr0 to0 to0 tl0;
       drop (dlist ptr0 to0 to0 []);
       // tl0 == []
       // this assume one is needed until we model null properly
       assume (ptr0 =!= null_dlist);

       // 2. ptr0.next <- ptr1
       write ptr0 (set_next c0 ptr1);

       write_prev ptr1 ptr0;

       intro_dlist_cons from0 ptr0 _ _ ptr1 _;
       drop (pure (tl0 == []));
       returnF #_
               (dlist from0 ptr0 null_dlist)
               (set_next c0 ptr1
                   :: set_prev hd1 ptr0
                   :: tl1)
     ) else (
       (** But, I can't write the other branch
           because it seems to want the pre-post to match exactly
           rather than be related by equiv **)
       // let l = concat_cons (concat #a)
       //              from0 ptr0 to0 c0 tl0
       //              from1 ptr1 hd1 tl1 in
       sladmit_depF ()
     )
