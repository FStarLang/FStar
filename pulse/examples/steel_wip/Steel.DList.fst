module Steel.DList
open Steel.Liar
open Steel.DList.Invariant

//We're trying to write this library in the "internal" language of Steel
//the front end + frame inference should elaborate into something like this
//If it does, then the proofs can be done with almost nothing in the SMT context
//except very basic stuff from Prims and Pervasives
//and application-specific stuff for this particular module (Steel.DList)
#set-options "--using_facts_from 'Prims FStar.Pervasives FStar.List Steel.DList' --log_queries --query_stats"
let new_dlist (#a:Type) (init:a)
  : Steel (t a & cell a)
    (requires
      empty_resource)
    (ensures fun pc ->
      dlist null_dlist (fst pc) null_dlist [snd pc])
    (requires fun _ -> True)
    (ensures fun _ pc _ ->
      data (snd pc) == init)
  = let cell = mk_cell null_dlist null_dlist init in
    let p =
      frame
        empty_resource
        (fun p -> pts_to p cell)
        (fun _ -> alloc_cell cell)
    in
    frame (pts_to p cell)
          (fun _ -> pts_to p cell <*> dlist p null_dlist null_dlist [])
          (fun _ -> intro_dlist_nil p null_dlist);
    intro_dlist_cons null_dlist p null_dlist cell [];
    p, cell

let read_head (#a:_) (from0:t a) (ptr0:t a) (to0: t a) (hd:cell a) (tl:list (cell a))
  : Steel (cell a)
    (requires
      dlist from0 ptr0 to0 (hd::tl))
    (ensures fun _ ->
      dlist from0 ptr0 to0 (hd::tl))
    (requires fun _ ->
      True)
    (ensures fun _ v _ ->
      v == hd)
  =  //1: unfold dlist to dlist cons
     elim_dlist_cons from0 ptr0 to0 hd tl;

     //2: read the ptr0 to get cell0
     let c0 =
       frame
         (pts_to ptr0 hd <*> dlist ptr0 (next hd) to0 tl)
         (fun _ -> pts_to ptr0 hd <*> dlist ptr0 (next hd) to0 tl)
         (fun _ -> read_ptr ptr0 hd) in

     //3: fold it back into a dlist
     intro_dlist_cons from0 ptr0 to0 hd tl;

     c0

//Not sure why this is necessary
//Without it, we get a bunch of additional trivial SMT queries
//Need to debug

irreducible
let hd = Steel.DList.Invariant.hd
irreducible
let tl = Steel.DList.Invariant.tl

let rec datas (l:list (cell 'a)) : list 'a =
  match l with
  | [] -> []
  | hd::tl -> data hd::datas tl
assume
val datas_append (l0 l1:list (cell 'a))
  : Lemma (datas (l0 @ l1) == datas l0 @ datas l1)
          [SMTPat (datas (l0 @ l1))]

assume
val append_cons (#a:_) (hd : cell a) (l0 l1:list (cell a))
  : Lemma (data hd :: datas (l0 @ l1) == datas (hd::l0) @ datas l1)
          [SMTPat (data hd :: datas (l0 @ l1))]

let test (r:resource) (c:cell unit) : St (t unit) r (fun p -> r <*> pts_to p c) =
  frame r
        (fun p -> r <*> pts_to p c)
        (fun _ -> alloc_cell c)

let drop (r:resource)
  : St unit
    (requires r)
    (ensures fun _ -> empty_resource)
  = reveal_empty_resource()

let rec concat (#a:Type)
               (from0:t a) (ptr0:t a) (to0: t a) (l0:list (cell a))
               (from1:t a) (ptr1:t a) (l1:list (cell a))
   : Steel (list (cell a))
     (requires
       dlist from0 ptr0 to0 l0 <*>
       dlist from1 ptr1 null_dlist l1)
     (ensures fun l ->
       dlist from0 ptr0 null_dlist l)
     (requires fun _ -> Cons? l0 /\ Cons? l1)
     (ensures fun _ l _ ->
       datas l == datas l0 @ datas l1)
   =
     let l = l0@l1 in

     //not naming these leads to unification failures in frame
     let hd0 = hd l0 in
     let tl0 = tl l0 in

     let hd1 = hd l1 in
     let tl1 = tl l1 in
     let to1 = null_dlist #a in

     //1: read the ptr0 to get cell0
     let c0 =
       frame
         (dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
         (fun _ -> dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
         (fun _ -> read_head from0 ptr0 to0 hd0 tl0)
     in

     //2: unfold dlist to dlist cons
     frame
       (dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
       (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1) //<--
       (fun _ -> elim_dlist_cons from0 ptr0 to0 hd0 tl0);

     if ptr_eq (next c0) to0
     then begin //we are at the end of l0
       // 3. invert dlist tl0 to dlist []
       frame
         (pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1)
         (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 to0 to0 [] <*> dlist from1 ptr1 to1 l1)
         (fun _ -> invert_dlist_nil_eq ptr0 (next hd0) to0 tl0);

       frame
         (pts_to ptr0 hd0 <*> dlist ptr0 to0 to0 [] <*> dlist from1 ptr1 to1 l1)
         (fun _ -> pts_to ptr0 hd0 <*> dlist from1 ptr1 to1 l1)
         (fun _ -> drop (dlist ptr0 to0 to0 []));

       // This is a long-winded way of saying:
       //   p0.next <- p1
       let c0' = mk_cell (prev c0) ptr1 (data c0) in
       frame
           (pts_to ptr0 hd0 <*> dlist from1 ptr1 to1 l1)
           (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 l1)
           (fun _ -> write_ptr ptr0 hd0 c0');


       let c1 =
         frame
           (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
           (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
           (fun _ -> read_head from1 ptr1 to1 hd1 tl1) in


       frame
           (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
           (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)
           (fun _ -> elim_dlist_cons from1 ptr1 to1 hd1 tl1);

       // This is a long-winded way of saying:
       //   p1.prev <- p0
       let c1' = mk_cell ptr0 (next c1) (data c1) in
       frame
           (pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)
           (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next hd1) to1 tl1)
           (fun _ -> write_ptr ptr1 hd1 c1');

       frame
           (pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next c1') to1 tl1)
           (fun _ -> pts_to ptr0 c0' <*> dlist ptr0 ptr1 to1 (c1'::tl1))
           (fun _ -> intro_dlist_cons ptr0 ptr1 to1 c1' tl1);

       intro_dlist_cons from0 ptr0 to1 c0' (c1'::tl1);

       let l = [c0'] @ (c1'::tl1) in
       assert (datas l1 == data c1' :: datas tl1);
       assert (datas l == datas [c0'] @ datas (c1'::tl1));
       assert (datas (l0 @ l1) == datas l0 @ datas l1);
       assert (datas l1 == datas (c1' :: tl1));
       assert (datas l0 == datas [c0']);
       assert (datas l == datas l0 @ datas l1);
       l
     end
     else begin
       //pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1
       //next c0 =!= t0
       frame
          (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
          (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
          (fun _ -> invert_dlist_cons_neq ptr0 (next c0) to0 tl0);

       let l =
         frame
           (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
           (fun l -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) null_dlist l)
           (fun _ -> concat ptr0 (next c0) to0 tl0 from1 ptr1 l1)
       in
       intro_dlist_cons from0 ptr0 null_dlist hd0 l;
       resource_assertion (dlist from0 ptr0 to1 (hd0::l));
       assert (datas l == datas tl0 @ datas l1);
       assert (datas (hd0::l) == data hd0 :: datas (tl0 @ l1));
       append_cons hd0 tl0 l1;
       hd0::l
     end

let snoc (#a:Type)
         (from0:t a) (ptr0:t a) (to0: t a) (l0:list (cell a))
         (v:a)
   : Steel (list (cell a))
     (requires
       dlist from0 ptr0 to0 l0)
     (ensures
       dlist from0 ptr0 null_dlist)
     (requires fun _ ->
       Cons? l0)
     (ensures fun _ l _ ->
       datas l == datas l0 @ datas [mk_cell null_dlist null_dlist v])
   = let pc =
       frame (dlist from0 ptr0 to0 l0)
             (fun pc -> dlist from0 ptr0 to0 l0 <*> dlist null_dlist (fst pc) null_dlist [snd pc])
             (fun _ -> new_dlist v) in

     concat from0 ptr0 to0 l0
            null_dlist (fst pc) [snd pc]

let cons (#a:Type)
         (from0:t a) (ptr0:t a) (l0:list (cell a))
         (v:a)
   : Steel (t a & list (cell a))
     (requires
       dlist from0 ptr0 null_dlist l0)
     (ensures fun pc ->
       dlist null_dlist (fst pc) null_dlist (snd pc))
     (requires fun _ ->
       Cons? l0)
     (ensures fun _ pc _ ->
       datas (snd pc) == datas [mk_cell null_dlist null_dlist v] @ datas l0)
   = let to0 = null_dlist in

     let pc =
       frame (dlist from0 ptr0 to0 l0)
             (fun pc -> dlist null_dlist (fst pc) null_dlist [snd pc] <*> dlist from0 ptr0 to0 l0)
             (fun _ -> new_dlist v) in

     let l =
       concat null_dlist (fst pc) null_dlist [snd pc]
              from0 ptr0 l0
     in
     fst pc, l
