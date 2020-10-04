module DList
open Steel.Memory
open Steel.Effect  
open Steel.FractionalPermission
open Steel.Reference
open DList.Invariant

assume val p : slprop u#1
assume val q : slprop u#1
assume val r : slprop u#1
assume val s : slprop u#1
assume val sladmit (#[@@framing_implicit] p:slprop)  (#[@@framing_implicit]q:slprop) (_:unit) : SteelT unit p (fun _ -> q)

let test_pq () : SteelT unit p (fun _ -> q) = sladmit()
let test_pr () : SteelT unit p (fun _ -> r) = test_pq(); sladmit()
let test_rs () : SteelT unit r (fun _ -> s) = sladmit()
let test_ps () : SteelT unit p (fun _ -> s) = test_pq(); sladmit(); test_rs()

let test_pr2 () : SteelT unit p (fun _ -> r) = let x = test_pq() in sladmit()

assume val sladmitf (#[@@framing_implicit] p:slprop)  (#[@@framing_implicit]q:slprop) (_:unit) : SteelF unit p (fun _ -> q) (fun _ -> True) (fun _ _ _ -> True)


let test_pq_f () : SteelT unit p (fun _ -> q) = sladmitf()
let test_pr_f () : SteelT unit p (fun _ -> r) = test_pq(); sladmitf()
let test_rs_f () : SteelT unit r (fun _ -> s) = sladmit()
let test_ps_f () : SteelT unit p (fun _ -> s) = test_pq(); sladmitf(); test_rs()

let test_pr2_f () : SteelT unit p (fun _ -> r) = let x = test_pq() in sladmitf()

assume val sladmit_dep (#a:_)
                       (p:slprop)              
                       (q:(a -> slprop))
       : SteelT a p q

assume val sladmit_depF (#a:_)
                       (#[@@framing_implicit] p:slprop)              
                       (#[@@framing_implicit] q:(a -> slprop))
                       (_:unit)
       : SteelF a p q (fun _ -> True) (fun _ _ _ -> True)

let return (#a:_)
                    (p:slprop)              
                    (q:(a -> slprop))
                    (x:a) 
    : Steel a p q
         (requires fun _ -> p == q x)
         (ensures fun _ y _ -> y == x)
    = change_slprop p (q x) (fun _ -> ());
      x
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
    return (dlist null_dlist p null_dlist [cell])
           (fun pc -> dlist null_dlist (fst pc) null_dlist [(snd pc)])
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

// let test (r:resource) (c:cell unit) : St (t unit) r (fun p -> r <*> pts_to p c) =
//   frame r
//         (fun p -> r <*> pts_to p c)
//         (fun _ -> alloc_cell c)

// let drop (r:resource)
//   : St unit
//     (requires r)
//     (ensures fun _ -> empty_resource)
//   = reveal_empty_resource()

assume
val concat_nil_l (#a:Type)
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

let concat_t a =
  (from0:t a) ->
  (ptr0:t a) ->
  (to0: t a) ->
  (hd0:cell a) ->
  (tl0:list (cell a)) ->
  (from1:t a) ->
  (ptr1:t a) ->
  (hd1:cell a) ->
  (tl1:list (cell a)) ->
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
     let l = aux ptr0 (next c0) to0 hd0 tl0' from1 ptr1 hd1 tl1 in
     assume (ptr0 =!= null_dlist);
     intro_dlist_cons from0 ptr0 null_dlist c0 l;
     c0::l

let rec concat (#a:Type)
               (from0:t a) (ptr0:t a) (to0: t a) (hd0:cell a) (tl0:list (cell a))
               (from1:t a) (ptr1:t a) (hd1:cell a) (tl1:list (cell a))
   : SteelT (list (cell a))
     (dlist from0 ptr0 to0 (hd0::tl0) `star`
      dlist from1 ptr1 null_dlist (hd1::tl1))
     (fun l ->
       dlist from0 ptr0 null_dlist l)
//       datas l == datas l0 @ datas l1)
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
         // invert_dlist_cons_neq ptr0 (next c0) to0 tl0;
         // let l = concat ptr0 (next c0) to0 tl0 from1 ptr1 hd1 l1 in
         // sladmit_depF #_ 
         //              #(pts_to ptr0 full_perm c0 `star`
         //                dlist ptr0 (next c0) null_dlist l)
         //              #(dlist from0 ptr0 null_dlist) 
         //              ())

//      if ptr_eq (next c0) to0
//      then begin //we are at the end of l0
//        // 3. invert dlist tl0 to dlist []
//        frame
//          (pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 to0 to0 [] <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> invert_dlist_nil_eq ptr0 (next hd0) to0 tl0);

//        frame
//          (pts_to ptr0 hd0 <*> dlist ptr0 to0 to0 [] <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> pts_to ptr0 hd0 <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> drop (dlist ptr0 to0 to0 []));

//        // This is a long-winded way of saying:
//        //   p0.next <- p1
//        let c0' = mk_cell (prev c0) ptr1 (data c0) in
//        frame
//            (pts_to ptr0 hd0 <*> dlist from1 ptr1 to1 l1)
//            (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 l1)
//            (fun _ -> write_ptr ptr0 hd0 c0');


//        let c1 =
//          frame
//            (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
//            (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
//            (fun _ -> read_head from1 ptr1 to1 hd1 tl1) in


//        frame
//            (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
//            (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)
//            (fun _ -> elim_dlist_cons from1 ptr1 to1 hd1 tl1);

//        // This is a long-winded way of saying:
//        //   p1.prev <- p0
//        let c1' = mk_cell ptr0 (next c1) (data c1) in
//        frame
//            (pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)
//            (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next hd1) to1 tl1)
//            (fun _ -> write_ptr ptr1 hd1 c1');

//        frame
//            (pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next c1') to1 tl1)
//            (fun _ -> pts_to ptr0 c0' <*> dlist ptr0 ptr1 to1 (c1'::tl1))
//            (fun _ -> intro_dlist_cons ptr0 ptr1 to1 c1' tl1);

//        intro_dlist_cons from0 ptr0 to1 c0' (c1'::tl1);

//        let l = [c0'] @ (c1'::tl1) in
//        assert (datas l1 == data c1' :: datas tl1);
//        assert (datas l == datas [c0'] @ datas (c1'::tl1));
//        assert (datas (l0 @ l1) == datas l0 @ datas l1);
//        assert (datas l1 == datas (c1' :: tl1));
//        assert (datas l0 == datas [c0']);
//        assert (datas l == datas l0 @ datas l1);
//        l
//      end
//      else begin
//        //pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1
//        //next c0 =!= t0
//        frame
//           (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
//           (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
//           (fun _ -> invert_dlist_cons_neq ptr0 (next c0) to0 tl0);

//        let l =
//          frame
//            (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
//            (fun l -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) null_dlist l)
//            (fun _ -> concat ptr0 (next c0) to0 tl0 from1 ptr1 l1)
//        in
//        intro_dlist_cons from0 ptr0 null_dlist hd0 l;
//        resource_assertion (dlist from0 ptr0 to1 (hd0::l));
//        assert (datas l == datas tl0 @ datas l1);
//        assert (datas (hd0::l) == data hd0 :: datas (tl0 @ l1));
//        append_cons hd0 tl0 l1;
//        hd0::l
//      end

// let snoc (#a:Type)
//          (from0:t a) (ptr0:t a) (to0: t a) (l0:list (cell a))
//          (v:a)
//    : Steel (list (cell a))
//      (requires
//        dlist from0 ptr0 to0 l0)
//      (ensures
//        dlist from0 ptr0 null_dlist)
//      (requires fun _ ->
//        Cons? l0)
//      (ensures fun _ l _ ->
//        datas l == datas l0 @ datas [mk_cell null_dlist null_dlist v])
//    = let pc =
//        frame (dlist from0 ptr0 to0 l0)
//              (fun pc -> dlist from0 ptr0 to0 l0 <*> dlist null_dlist (fst pc) null_dlist [snd pc])
//              (fun _ -> new_dlist v) in

//      concat from0 ptr0 to0 l0
//             null_dlist (fst pc) [snd pc]

// let cons (#a:Type)
//          (from0:t a) (ptr0:t a) (l0:list (cell a))
//          (v:a)
//    : Steel (t a & list (cell a))
//      (requires
//        dlist from0 ptr0 null_dlist l0)
//      (ensures fun pc ->
//        dlist null_dlist (fst pc) null_dlist (snd pc))
//      (requires fun _ ->
//        Cons? l0)
//      (ensures fun _ pc _ ->
//        datas (snd pc) == datas [mk_cell null_dlist null_dlist v] @ datas l0)
//    = let to0 = null_dlist in

//      let pc =
//        frame (dlist from0 ptr0 to0 l0)
//              (fun pc -> dlist null_dlist (fst pc) null_dlist [snd pc] <*> dlist from0 ptr0 to0 l0)
//              (fun _ -> new_dlist v) in

//      let l =
//        concat null_dlist (fst pc) null_dlist [snd pc]
//               from0 ptr0 l0
//      in
//      fst pc, l
