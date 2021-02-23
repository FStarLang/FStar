(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author(s): N. Swamy
*)
module DList.Invariant
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot
module U = Steel.Utils

module ST = Steel.Memory.Tactics
module T = FStar.Tactics

assume
val rewrite_pure (p q:prop)
  : Lemma (requires (p <==> q))
          (ensures (pure p `equiv` pure q))

assume
val combine_pure (p q:prop)
  : Lemma ((pure p `star` pure q) `equiv` pure (p /\ q))

assume
val use_pure (p :prop) (q r:slprop) (_:squash (p ==> q `equiv` r))
  : Lemma ((pure p `star` q) `equiv` (pure p `star` r))

assume
val utils (_:unit)
  : Lemma ((forall p q r. ((p `star` q) `star` r) == (p `star` (q `star` r))) /\
           (forall p q. (p `star` q) == (q `star` p)) /\
           (forall p q.{:pattern (p `equiv` q)} (p `equiv` q) <==> p == q) /\
           (forall (a b:prop). {:pattern (pure a `star` pure b)}
                          ((pure a) `star` (pure b)) `equiv` pure (a /\ b)))

let rev_cons #a (x:a) (xs:list a)
  : Lemma (List.rev (x::xs) == List.snoc (List.rev xs, x))
  = admit()

let rev_snoc #a (x:a) (xs:list a)
  : Lemma (let prefix, last = List.unsnoc (x::xs) in
           List.rev (x::xs) == last :: List.rev prefix)
  = admit()

let rev_involutive #a (xs:list a)
  : Lemma (List.rev (List.rev xs) == xs)
  = admit()

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  prev: ref (cell a);
  next: ref (cell a);
  data: a;
}
#pop-options


let prev (c:cell 'a) : t 'a = c.prev
let next (c:cell 'a) : t 'a = c.next
let data (c:cell 'a) : 'a = c.data
let mk_cell (p n: t 'a) (d:'a) = {
  prev = p;
  next = n;
  data = d
}
let hd l = Cons?.hd l
let tl l = Cons?.tl l

let ptr_eq (#a:Type) (x y:t a) = admit()
let pts_to #a (x:t a) (c:cell a) = pts_to x full_perm c

let pts_to_injective #a (x y:t a) (c0 c1:cell a)
  : Lemma ((pts_to x c0 `star` pts_to y c1) `equiv`
           ((pts_to x c0 `star` pts_to y c1) `star` pure (x =!= y)))
  = admit()

////////////////////////////////////////////////////////////////////////////////
// Main dlist invariant
////////////////////////////////////////////////////////////////////////////////
let rec dlist_cons (#a:Type) (previous :t a)
                             (cur  :t a)
                             (last :t a)
                             (right:t a)
                             (xs:list (cell a))
    : Tot slprop (decreases xs)
    = match xs with
      | [] ->
        pure (last == previous /\
              cur == right)

      | x :: xs ->
        pure (prev x == previous) `star`
        pts_to cur x `star`
        dlist_cons cur (next x) last right xs

let rec dlist_snoc (#a:Type) (left:t a)
                             (last:t a)
                             (cur:t a)
                             (nxt:t a)
                             (xs:list (cell a))
    : Tot slprop (decreases xs)
    = match xs with
      | []  ->
        pure (last == nxt /\
              cur == left)

      | x :: xs ->
        pure (next x == nxt) `star`
        pts_to cur x `star`
        dlist_snoc left last (prev x) cur xs


let dlist_cons_snoc_nil #a (left front back right: t a)
  : Lemma (dlist_cons left front back right [] `equiv`
           dlist_snoc left front back right [])
  = calc
    (equiv) {
         dlist_cons left front back right [];
    (equiv) { }
         pure (back == left /\
               front == right);
    (equiv) { _ by (T.mapply (`rewrite_pure)) }
         pure (front == right /\
               back == left);
    (equiv) { }
         dlist_snoc left front back right [];
    }


let rec dlist_snoc_snoc (#a:Type) (left:t a)
                                  (last:t a)
                                  (cur:t a)
                                  (right:t a)
                                  (xs:list (cell a))
                                  (x:cell a)
  : Lemma (ensures
          (dlist_snoc left last cur right (List.snoc (xs, x)) `equiv`
            (pure (prev x == left) `star`
             pts_to last x `star`
             dlist_snoc last (next x) cur right xs)))
          (decreases (List.length xs))
  = match xs with
    | [] ->
      assert (List.snoc (xs, x) == [x]);
      calc
      (equiv) {
           dlist_snoc left last cur right (List.snoc (xs, x));
      (equiv) { (* def *) }
           pure (next x == right) `star`
           pts_to cur x `star`
           dlist_snoc left last (prev x) cur [];
      (equiv) { (* def *) }
           pure (next x == right) `star`
           pts_to cur x `star`
           pure (last == cur /\
                 prev x == left);
       (equiv) { (* AC *) _ by (ST.canon()) }
           pure (next x == right) `star`
           pure (last == cur /\
                 prev x == left) `star`
           pts_to cur x;
       (equiv) { (* pure regroup *) utils () }
           pure (next x == right /\ (last == cur /\ prev x == left)) `star`
           pts_to cur x;
       (equiv) {  (* pure regroup *)
                  calc
                  (equiv) {
                    pure (next x == right /\ (last == cur /\ prev x == left));
                  (equiv) { _ by (T.mapply (`rewrite_pure)) }
                    pure (prev x == left /\ (next x == right /\ cur == last));
                  };
                  utils()
               }
           pure (prev x == left) `star`
           pure (next x == right /\ cur == last) `star`
           pts_to cur x;
       (equiv) { (* AC *) _ by (ST.canon()) }
           pure (prev x == left) `star`
           (pure (next x == right /\ cur == last) `star`
            pts_to cur x);
       (equiv) { (* rewrite ... main "interesting" step *)
                  calc
                  (equiv) {
                       pure (next x == right /\ cur == last) `star`
                       pts_to cur x;
                  (equiv) { _ by (T.mapply (`use_pure)) }
                       pure (next x == right /\ cur == last) `star`
                       pts_to last x;
                  };
                  utils()
               }
           pure (prev x == left) `star`
           (pure (next x == right /\ cur == last) `star`
            pts_to last x);
       (equiv) { (* AC *) _ by (ST.canon()) }
           pure (prev x == left) `star`
           pts_to last x `star`
           pure (next x == right /\ cur == last);
       }

    | hd::xs' ->
      calc (equiv) {
        dlist_snoc left last cur right (List.snoc (hd::xs', x));
      (equiv) { (* defn *) }
        pure (next hd == right) `star`
        pts_to cur hd `star`
        dlist_snoc left last (prev hd) cur (List.snoc (xs', x));
      (equiv) { (* IH *)
                utils ();
                dlist_snoc_snoc left last (prev hd) cur xs' x
              }
        pure (next hd == right) `star`
        pts_to cur hd `star`
        (pure (prev x == left) `star`
         pts_to last x `star`
         dlist_snoc last (next x) (prev hd) cur xs');
      (equiv) { _ by (ST.canon()) }
        pure (prev x == left) `star`
        pts_to last x `star`
        (pure (next hd == right) `star`
         pts_to cur hd `star`
         dlist_snoc last (next x) (prev hd) cur xs');
      (equiv) { }
         (pure (prev x == left) `star`
          pts_to last x `star`
          dlist_snoc last (next x) cur right xs);
      }

let rec dlist_cons_snoc (#a:Type) (left :t a)
                                  (head  :t a)
                                  (tail :t a)
                                  (right:t a)
                                  (l:list (cell a))
  : Lemma (ensures dlist_cons left head tail right l `equiv`
                   dlist_snoc left head tail right (List.rev l))
          (decreases l)
  = match l with
    | [] -> dlist_cons_snoc_nil left head tail right
    | x :: xs ->
      dlist_cons_snoc head (next x) tail right xs;
      rev_cons x xs;
      dlist_snoc_snoc left head tail right (List.rev xs) x;
      utils()

let last #a (xs:list (cell a) { Cons? xs }) = snd (List.unsnoc xs)
let first #a (xs:list (cell a) { Cons? xs }) = List.Tot.Base.hd xs
let dlist_cons_tail (#a:_) (left head tail right:t a) (xs:list (cell a) { Cons? xs })
  : Lemma (
      let prefix, last = List.unsnoc xs in
      dlist_cons left head tail right xs `equiv`
      (pure (next last == right) `star`
       pts_to tail last `star`
       dlist_cons left head (prev last) tail prefix))
  = let x :: xs' = xs in
    rev_cons x xs';
    let prefix, last = List.unsnoc xs in
    rev_snoc x xs';
    calc
    (equiv) {
         dlist_cons left head tail right xs;
    (equiv) { _ by (T.mapply (`dlist_cons_snoc)) }
         dlist_snoc left head tail right (List.rev xs);
    (equiv) { }
         dlist_snoc left head tail right (last :: List.rev prefix);
    (equiv) { }
         pure (next last == right) `star`
         pts_to tail last `star`
         dlist_snoc left head (prev last) tail (List.rev prefix);
    (equiv) { utils();
              dlist_cons_snoc left head (prev last) tail prefix }
         pure (next last == right) `star`
         pts_to tail last `star`
         dlist_cons left head (prev last) tail prefix;
    }

let dlist_snoc_head (#a:_) (left head tail right:t a) (xs:list (cell a) { Cons? xs })
  : Lemma (
      let prefix, last = List.unsnoc xs in
      dlist_snoc left head tail right xs `equiv`
      (pure (prev last == left) `star`
       pts_to head last `star`
       dlist_snoc head (next last) tail right prefix))
  = let prefix, last = List.unsnoc xs in
    dlist_snoc_snoc left head tail right prefix last

let dlist_cons_last (#a:Type)
                    (left head tail right:t a)
                    (x:cell a)
                    (xs:list (cell a))
  : Lemma
      (equiv (pure (head == tail) `star`
              dlist_cons left head tail right (x::xs))
             (pure (head == tail /\ xs == []) `star`
              dlist_cons left head tail right (x::xs)))
  = match xs with
    | [] ->
      utils();
      assert (pure (head == tail) `equiv`
              pure (head == tail /\ xs == []))
          by (T.mapply (`rewrite_pure))

    | _ ->
      let xs : (xs:list _ { Cons? xs }) = xs in
      let prefix, last = List.unsnoc xs in
      calc
      (equiv) {
           pure (head == tail) `star`
           dlist_cons left head tail right (x::xs);
      (equiv) { }
           pure (head == tail) `star`
           (pure (prev x == left) `star`
            pts_to head x `star`
            dlist_cons head (next x) tail right xs);
      (equiv) {
                calc
                (equiv) {
                     dlist_cons head (next x) tail right xs;
                (equiv) { dlist_cons_tail head (next x) tail right xs }
                    (pure (next last == right) `star`
                     pts_to tail last `star`
                     dlist_cons head (next x) (prev last) tail prefix);
                };
                utils()
              }
           pure (head == tail) `star`
           (pure (prev x == left) `star`
            pts_to head x `star`
            (pure (next last == right) `star`
             pts_to tail last `star`
             dlist_cons head (next x) (prev last) tail prefix));
       (equiv) { _ by (ST.canon()) }
          (pts_to head x `star` pts_to tail last) `star`
           (pure (head == tail) `star`
            pure (prev x == left) `star`
            pure (next last == right) `star`
            dlist_cons head (next x) (prev last) tail prefix);
       (equiv) { pts_to_injective head tail x last; utils () }
          (pts_to head x `star` pts_to tail last `star` pure (head =!= tail)) `star`
           (pure (head == tail) `star`
            pure (prev x == left) `star`
            pure (next last == right) `star`
            dlist_cons head (next x) (prev last) tail prefix);
       (equiv) { _ by (ST.canon()) }
          (pure (head == tail) `star` pure (head =!= tail)) `star`
          (pts_to head x `star` pts_to tail last `star`
            pure (prev x == left) `star`
            pure (next last == right) `star`
            dlist_cons head (next x) (prev last) tail prefix);
       (equiv) { utils () }
          pure (head == tail /\ head =!= tail) `star`
          (pts_to head x `star` pts_to tail last `star`
            pure (prev x == left) `star`
            pure (next last == right) `star`
            dlist_cons head (next x) (prev last) tail prefix);
       (equiv) { _ by (T.mapply (`use_pure)) }
          pure (head == tail /\ head =!= tail) `star`
          pure False;
       (equiv) { _ by (T.mapply (`combine_pure)) }
          pure ((head == tail /\ head =!= tail) /\ False);
       (equiv) { _ by (T.mapply (`rewrite_pure)) }
          pure False;
      };

      calc
      (equiv) {
           pure (head == tail /\ xs == []) `star`
           dlist_cons left head tail right (x::xs);
      (equiv)  { _ by (T.mapply (`use_pure)) }
           pure (head == tail /\ xs == []) `star`
           pure False;
       (equiv) { _ by (T.mapply (`combine_pure)) }
          pure ((head == tail /\ xs == []) /\ False);
       (equiv) { _ by (T.mapply (`rewrite_pure)) }
          pure False;
      }

let dlist_snoc_last (#a:Type)
                        (left head tail right:t a)
                        (x:cell a)
                        (xs:list (cell a))
  : Lemma
      (equiv (pure (head == tail) `star`
              dlist_snoc left head tail right (x::xs))
             (pure (head == tail /\ xs == []) `star`
              dlist_snoc left head tail right (x::xs)))
  = dlist_cons_snoc left head tail right (x :: xs);
    let prefix, last = List.unsnoc (x :: xs) in
    rev_snoc x xs;
    rev_involutive (x :: xs);
    dlist_cons_last left head tail right last (List.rev prefix);
    calc
    (equiv) {
         pure (head == tail) `star`
         dlist_snoc left head tail right (x::xs);
    (equiv) { dlist_cons_snoc left head tail right (last :: List.rev prefix); utils() }
         pure (head == tail) `star`
         dlist_cons left head tail right (last :: List.rev prefix);
    (equiv) { _ by (T.mapply (`dlist_cons_last)) }
         pure (head == tail /\ List.rev prefix == []) `star`
         dlist_cons left head tail right (last :: List.rev prefix);
    (equiv) { dlist_cons_snoc left head tail right (last :: List.rev prefix); utils() }
         pure (head == tail /\ List.rev prefix == []) `star`
         dlist_snoc left head tail right (x :: xs);
    (equiv) {
              calc
              (equiv) {
                pure (head == tail /\ List.rev prefix == []);
              (equiv) { rewrite_pure (head == tail /\ List.rev prefix == []) (head == tail /\ xs == []) }
                pure (head == tail /\ xs == []);
              };
              utils()
            }
         pure (head == tail /\ xs == []) `star`
         dlist_snoc left head tail right (x :: xs);
    }

let stronger (p q: slprop) = forall m. interp p m ==> interp q m
let stronger_star_r (p q r:slprop)
  : Lemma (requires q `stronger` r)
          (ensures  (p `star` q) `stronger` (p `star` r)) = admit()
let stronger_star_l (p q r:slprop)
  : Lemma (requires p `stronger` q)
          (ensures  (p `star` r) `stronger` (q `star` r)) = admit()
let stronger_drop_l (p q:slprop)
  : Lemma (ensures  (p `star` q) `stronger` q) = admit()

let rec dlist_cons_concat #a (left head1 tail1 mid:t a) (xs1:_)
                             (tail2 right:t a) (xs2:_)
  : Lemma (ensures
             stronger (dlist_cons left head1 tail1 mid xs1 `star`
                       dlist_cons tail1 mid tail2 right xs2)
                      (dlist_cons left head1 tail2 right (xs1 @ xs2)))
          (decreases xs1)
  = match xs1 with
    | [] ->
      calc
      (stronger) {
        dlist_cons left head1 tail1 mid [] `star`
        dlist_cons tail1 mid tail2 right xs2;
      (equiv) {}
        pure (tail1 == left /\
              head1 == mid) `star`
        dlist_cons tail1 mid tail2 right xs2;
      (equiv) { _ by (T.mapply (`use_pure)) }
        pure (tail1 == left /\
              head1 == mid) `star`
        dlist_cons left head1 tail2 right xs2;
      (stronger) { _ by (T.mapply (`stronger_drop_l)) }
        dlist_cons left head1 tail2 right xs2;
      }

    | x :: xs1' ->
      let xs1' : (l:list _ {l << xs1}) = xs1' in
      calc
      (stronger) {
          dlist_cons left head1 tail1 mid xs1 `star`
          dlist_cons tail1 mid tail2 right xs2;
      (equiv) {}
        (pure (prev x == left) `star`
         pts_to head1 x `star`
         dlist_cons head1 (next x) tail1 mid xs1') `star`
         dlist_cons tail1 mid tail2 right xs2;
      (equiv) { _ by (ST.canon()) }
         pure (prev x == left) `star`
         pts_to head1 x `star`
         (dlist_cons head1 (next x) tail1 mid xs1' `star`
          dlist_cons tail1 mid tail2 right xs2);
      (stronger) {
                   _ by (T.mapply (`stronger_star_r);
                         T.mapply (`dlist_cons_concat))
              }
        (pure (prev x == left) `star`
         pts_to head1 x `star`
         dlist_cons head1 (next x) tail2 right (xs1' @ xs2));
      (equiv) { }
         dlist_cons left head1 tail2 right (xs1 @ xs2);
      }

#push-options "--query_stats"
assume
val equiv_pure_emp (_:unit) : Lemma (equiv (pure True) emp)
let dlist_cons_nil (#a:_) (left right:t a)
  : Lemma (equiv emp (dlist_cons left right left right []))
  = calc
    (equiv) {
       dlist_cons left right left right [];
    (==) { _ by (T.norm [delta;zeta]; T.trefl()) }
       pure (left == left /\
             right == right);
    (equiv) { _ by (T.mapply (`rewrite_pure)) }
       pure True;
    (equiv) { _ by (T.mapply (`equiv_pure_emp)) }
       emp;
    }

let intro_dlist_nil' (#a:Type) #u (left right:t a)
  : SteelAtomicT unit u unobservable
      emp
      (fun _ -> dlist_cons left right left right [])
  = change_slprop _ _ (fun _ -> dlist_cons_nil left right)

let intro_pure_l (p:prop) (q:slprop)
  : Lemma (requires p)
          (ensures (q `equiv` (pure p `star` q)))
  = admit()

let dlist_cons_cons (#a:_) (head tail right:t a) (hd: cell a) (xs:_)
  : Lemma (equiv (pts_to head hd `star`
                  dlist_cons head (next hd) tail right xs)
                 (dlist_cons (prev hd) head tail right (hd::xs)))
  = calc
    (equiv) {
       pts_to head hd `star`
       dlist_cons head (next hd) tail right xs;
    (equiv) { _ by (T.mapply (`intro_pure_l)) }
      pure (prev hd == prev hd) `star`
      (pts_to head hd `star`
       dlist_cons head (next hd) tail right xs);
    (equiv) { _ by (ST.canon()) }
      pure (prev hd == prev hd) `star`
      pts_to head hd `star`
      dlist_cons head (next hd) tail right xs;
    (==) { _ by (T.norm [delta; zeta]; T.trefl()) }
      dlist_cons (prev hd) head tail right (hd::xs);
    }


let intro_dlist_cons_cons #a #u (head tail right:t a) (hd: cell a) (xs:_)
  : SteelAtomicT unit u unobservable
       (pts_to head hd `star`
        dlist_cons head (next hd) tail right xs)
       (fun _ ->
        dlist_cons (prev hd) head tail right (hd::xs))
  = change_slprop _ _ (fun m -> dlist_cons_cons head tail right hd xs)


let new_dlist (#a:Type) (init:a)
  : Steel (t a & cell a)
    emp
    (fun pc -> dlist_cons null (fst pc) (fst pc) null [snd pc])
    (requires fun _ -> True)
    (ensures fun _ pc _ -> data (snd pc) == init)
  = let cell = mk_cell null_dlist null_dlist init in
    let p = alloc cell in
    intro_dlist_nil' p null_dlist;
    slassert (pts_to p cell `star` dlist_cons p null_dlist p null_dlist []);
    sladmit()


    // intro_dlist_cons_cons p p null_dlist cell [];

    // sladmit()

    // U.pts_to_not_null p;
    // intro_dlist_nil p null_dlist;
    // change_slprop (dlist p null_dlist null_dlist [])
    //               (dlist p (next cell) null_dlist [])
    //               (fun _ -> ());
    // intro_dlist_cons null_dlist p null_dlist cell [];
    // let pc = p, cell in
    // pc

// let elim_dlist_nil (#a:Type) (left ptr right:t a)
//    : SteelT unit
//      (dlist left ptr right [])
//      (fun _ -> pure (right == ptr))
//    = change_slprop (dlist left ptr right [])
//                    (pure (right == ptr))
//                    (fun m -> pure_interp (ptr == right) m;
//                           norm_spec [delta;zeta] ((dlist left ptr right [])))


// let intro_star_pure (p:slprop) (q:prop) (h:mem)
//   : Lemma (interp p h /\ q ==> interp (p `star` pure q) h)
//   = let open Steel.Memory in
//     emp_unit p;
//     pure_star_interp p q h

// let dlist_right_right_nil (#a:Type) (left right:t a) (l:list (cell a)) (m:mem)
//   : Lemma
//     (requires interp (dlist left right right l) m)
//     (ensures interp (dlist left right right [] `star` pure (l == [])) m)
//   = pure_interp (right == right) m;
//     pure_interp (right =!= right) m;
//     pure_interp (l == []) m;
//     match l with
//     | [] -> intro_star_pure (dlist left right right []) (l == []) m
//     | hd::tl -> norm_spec [delta;zeta] (dlist left right right (hd::tl))

// let invert_dlist_nil_eq (#a:Type) (left ptr right:t a) (l:list (cell a))
//     : Steel unit
//             (dlist left ptr right l)
//             (fun _ -> dlist left right right [] `star` pure (l==[]))
//             (requires fun _ -> ptr == right)
//             (ensures fun _ _ _ -> True)
//     = change_slprop (dlist left ptr right l)
//                     (dlist left right right l)
//                     (fun _ -> ());
//       change_slprop (dlist left right right l)
//                     (dlist left right right [] `star` pure (l == []))
//                     (dlist_right_right_nil left right l)

// let intro_dlist_cons (#a:Type) (left:t a)
//                                (ptr:t a)
//                                (right:t a)
//                                (hd: cell a)
//                                (tl: list (cell a))
//    : Steel unit
//      (pts_to ptr full_perm hd `star` dlist ptr (next hd) right tl)
//      (fun _ -> dlist left ptr right (hd::tl))
//      (requires fun _ ->
//        prev hd == left /\
//        ptr =!= right)
//      (ensures fun _ _ _ -> True)
//    = change_slprop emp (pure (prev hd == left)) (fun m -> pure_interp (prev hd == left) m);
//      change_slprop emp (pure (right =!= ptr)) (fun m -> pure_interp (right =!= ptr) m);
//      change_slprop  (pure (right =!= ptr) `star`
//                      pts_to ptr full_perm hd `star`
//                      pure (prev hd == left) `star`
//                      dlist ptr (next hd) right tl)
//                     (dlist left ptr right (hd::tl))
//                     (fun _ -> norm_spec [delta;zeta] (dlist left ptr right (hd::tl)))

// let elim_dlist_cons (#a:Type) (left:t a)
//                               (ptr:t a)
//                               (right:t a)
//                               (hd:cell a)
//                               (tl:list (cell a))
//    = change_slprop  (dlist left ptr right (hd::tl))
//                     (pure (right =!= ptr) `star`
//                      pts_to ptr full_perm hd `star`
//                      pure (prev hd == left) `star`
//                      dlist ptr (next hd) right tl)
//                     (fun _ -> norm_spec [delta;zeta] (dlist left ptr right (hd::tl)));
//      U.elim_pure (right =!= ptr);
//      U.elim_pure (prev hd == left)

// let lemma_invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a)) (m:mem)
//   : Lemma
//     (requires interp (dlist left ptr right l) m /\ ptr =!= right)
//     (ensures interp (dlist left ptr right l `star` pure (Cons? l == true)) m)
//   = match l with
//     | [] ->
//       norm_spec [delta;zeta] (dlist left ptr right []);
//       assert (interp (dlist left ptr right []) m);
//       pure_interp (right == ptr) m
//     | hd::tl ->
//       intro_star_pure (dlist left ptr right l) (Cons? l == true) m

// let invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a))
//     : Steel unit
//      (requires
//        dlist left ptr right l)
//      (ensures fun _ ->
//        dlist left ptr right l)
//      (requires fun _ ->
//        ptr =!= right)
//      (ensures fun _ _ _ ->
//        Cons? l == true)
//    = change_slprop (dlist left ptr right l)
//                    (dlist left ptr right l `star` pure (Cons? l == true))
//                    (lemma_invert_dlist_cons_neq left ptr right l);
//      U.elim_pure (Cons? l == true)


// ////////////////////////////////////////////////////////////////////////////////

// let dlist_not_null (#a:Type)
//                    (#left:t a)
//                    (#right:t a)
//                    (#rep:list (cell a))
//                    (p:t a)
//   = U.lift_lemma (dlist left p right rep)
//                  ((Cons? rep) == true)
//                  (fun m -> if Cons? rep
//                         then ()
//                         else (assert (p =!= right);
//                               lemma_invert_dlist_cons_neq left p right rep m);
//                               Steel.Memory.pure_star_interp
//                                 (dlist left p right rep)
//                                 (Cons? rep == true)
//                                 m);
//     let hd :: tl = rep in
//     change_slprop (dlist left p right rep)
//                   (dlist left p right (hd :: tl))
//                   (fun _ -> ());
//     elim_dlist_cons left p right hd tl;
//     U.pts_to_not_null #_ #_ #full_perm #(Ghost.hide hd) p;
//     intro_dlist_cons left p right hd tl;
//     change_slprop (dlist left p right (hd :: tl))
//                   (dlist left p right rep)
//                   (fun _ -> ())
