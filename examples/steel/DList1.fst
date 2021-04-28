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
module DList1

open FStar.Ghost
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

let stronger (p q: slprop) = forall m. interp p m ==> interp q m
let stronger_star_r (p q r:slprop)
  : Lemma (requires q `stronger` r)
          (ensures  (p `star` q) `stronger` (p `star` r)) = admit()
let stronger_star_l (p q r:slprop)
  : Lemma (requires p `stronger` q)
          (ensures  (p `star` r) `stronger` (q `star` r)) = admit()
let stronger_drop_l (p q:slprop)
  : Lemma (ensures  (p `star` q) `stronger` q) = admit()

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


let intro_pure_l (p:prop) (q:slprop)
  : Lemma (requires p)
          (ensures (q `equiv` (pure p `star` q)))
  = admit()

let elim_pure (#p:prop) #u ()
  : SteelGhost unit u
                (pure p) (fun _ -> emp)
                (requires fun _ -> True)
                (ensures fun _ _ _ -> p)
  = let _ = Steel.Effect.Atomic.elim_pure p in ()

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  prev: ref (cell a);
  next: ref (cell a);
  data: a;
}
and t a = ref (cell a)
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
[@@__reduce__]
let pts_to #a (x:t a) (c:erased (cell a)) = pts_to x full_perm c

let pts_to_injective #a (x y:t a) (c0 c1:cell a)
  : Lemma ((pts_to x c0 `star` pts_to y c1) `equiv`
           ((pts_to x c0 `star` pts_to y c1) `star` pure (x =!= y)))
  = admit()

////////////////////////////////////////////////////////////////////////////////
// Main dlist invariant
////////////////////////////////////////////////////////////////////////////////
let rec dlist_cons (#a:Type) ([@@@smt_fallback]previous :t a)
                             ([@@@smt_fallback]cur  :t a)
                             ([@@@smt_fallback]last :t a)
                             ([@@@smt_fallback]right:t a)
                             ([@@@smt_fallback]xs:list (cell a))
    : Tot slprop (decreases xs)
    = match xs with
      | [] ->
        pure (last == previous /\
              cur == right)

      | x :: xs ->
        pure (prev x == previous) `star`
        pts_to cur x `star`
        dlist_cons cur (next x) last right xs

let rec dlist_snoc (#a:Type) ([@@@smt_fallback]left:t a)
                             ([@@@smt_fallback]last:t a)
                             ([@@@smt_fallback]cur:t a)
                             ([@@@smt_fallback]nxt:t a)
                             ([@@@smt_fallback]xs:list (cell a))
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
  : SteelGhostT unit u
      emp
      (fun _ -> dlist_cons left right left right [])
  = change_slprop _ _ (fun _ -> dlist_cons_nil left right)

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

let dlist_snoc_cons (#a:_) (left tail head:t a) (hd: cell a) (xs:_)
  : Lemma (equiv (pts_to head hd `star`
                  dlist_snoc left tail (prev hd) head xs)
                 (dlist_snoc left tail head (next hd) (hd::xs)))
  = calc
    (equiv) {
       pts_to head hd `star`
       dlist_snoc left tail (prev hd) head xs;
    (equiv) { _ by (T.mapply (`intro_pure_l)) }
      pure (next hd == next hd) `star`
      (pts_to head hd `star`
       dlist_snoc left tail (prev hd) head xs);
    (equiv) { _ by (ST.canon()) }
      pure (next hd == next hd) `star`
      pts_to head hd `star`
      dlist_snoc left tail (prev hd) head xs;
    (==) { _ by (T.norm [delta; zeta]; T.trefl()) }
      dlist_snoc left tail head (next hd) (hd::xs);
    }


let econs #a (x:erased a) (xs:erased (list a)) = hide (reveal x :: reveal xs)

let intro_dlist_cons_cons #a #u (head tail right:t a) (hd: erased (cell a)) (xs:erased (list (cell a)))
  : SteelGhostT unit u
       (pts_to head hd `star`
        dlist_cons head (next hd) tail right xs)
       (fun _ ->
        dlist_cons (prev hd) head tail right (econs hd xs))
  = change_slprop _ _ (fun m -> dlist_cons_cons head tail right hd xs)

let intro_dlist_snoc_cons #a #u (left tail head:t a) (hd: erased (cell a)) (xs:erased (list (cell a)))
  : SteelGhostT unit u
       (pts_to head hd `star`
        dlist_snoc left tail (prev hd) head xs)
       (fun _ ->
        dlist_snoc left tail head (next hd) (econs hd xs))
  = change_slprop _ _ (fun m -> dlist_snoc_cons left tail head hd xs)
#push-options "--ide_id_info_off"
let enil #a (x:erased a) : erased (list a) = hide [reveal x]

let new_dlist' (#a:Type) (init:a)
  : Steel (t a & Ghost.erased (cell a))
    emp
    (fun pc -> dlist_cons null (fst pc) (fst pc) null (enil (snd pc)))
    (requires fun _ -> True)
    (ensures fun _ pc _ -> data (snd pc) == init)
  = let cell = mk_cell null null init in
    let p = alloc cell in
    intro_dlist_nil' p null;
    intro_dlist_cons_cons p p null cell [];
    return (p, hide cell)

let elist a = erased (list a)
let datas #a (l:elist (cell a)) : elist a = hide (List.Tot.map (fun x -> x.data) (reveal l))
let eappend #a (l0 l1:elist a) : elist a = hide (reveal l0 @ reveal l1)
let erev #a (l:elist a) : elist a = hide (List.rev (reveal l))
let ecell a = erased (cell a)
let esnoc #a (xs:erased (list a)) (x:erased a) = hide (List.snoc (reveal xs, reveal x))

assume
val elim_dlist_cons_tail (#a:_) (#u:_) (#left #tail #right: t a) (#xs:Ghost.erased (list _)) (head:t a)
    : SteelGhost (erased (ecell a & elist (cell a))) u
        (dlist_cons left head tail right xs)
        (fun x ->
          pts_to tail (fst x) `star`
          dlist_snoc left head (prev (fst x)) tail (snd x))
        (requires fun _ -> Cons? xs == true)
        (ensures fun _ x _ -> econs (fst x) (snd x) == erev xs /\ next (fst x) == right)

assume
val elim_dlist_cons_head (#a:_) (#u:_) (#left #tail #right: t a) (#xs:Ghost.erased (list _)) (head:t a)
    : SteelGhost (erased (ecell a & elist (cell a))) u
        (dlist_cons left head tail right xs)
        (fun x ->
          pts_to head (fst x) `star`
          dlist_cons head (next (fst x)) tail right (snd x))
        (requires fun _ -> Cons? xs == true)
        (ensures fun _ x _ -> econs (fst x) (snd x) == xs /\ prev (fst x) == left)

let erev_cons (#a:_) (e:elist a) : Lemma (requires Cons? e) (ensures Cons? (erev e)) = admit ()

let datas_rev_snoc_cons #a (xs ys:elist (cell a))
                           (x y:ecell a)
                           (x' y':ecell a)
  : Lemma (requires x.data == x'.data /\ y.data == y'.data)
          (ensures datas (esnoc xs x `eappend` econs y ys) ==
                   datas (esnoc xs x' `eappend` econs y' ys))
  = admit()

let concat (#a:_) (left head tail right: t a)
                  (left' head' tail' right': t a)
                  (xs xs':Ghost.erased (list (cell a)))
  : Steel (elist (cell a))
          (dlist_cons left head tail right xs `star`
           dlist_cons left' head' tail' right' xs')
          (fun r -> dlist_cons left head tail' right' (reveal r))
          (requires fun _ -> Cons? xs /\ Cons? xs')
          (ensures fun _ r _ -> datas r == datas (eappend xs xs'))
  = erev_cons xs;
    let r = elim_dlist_cons_tail head in
    slassert (pts_to tail (fst r) `star`
              dlist_snoc left head (prev (fst r)) tail (snd r));
    let old = read tail in
    let c = { old with next = head' } in
    assert (erev xs == econs old (snd r));
    rev_involutive xs;
    assert (xs == erev (econs old (snd r)));
    rev_cons old (snd r);
    assert (xs == esnoc (erev (snd r)) old);
    write tail c;
    change_slprop
      (dlist_snoc left head (prev (fst r)) tail (snd r))
      (dlist_snoc left head (prev (Ghost.reveal (Ghost.hide c))) tail (snd r))
      (fun _ -> ());
    intro_dlist_snoc_cons left head tail (Ghost.hide c) (snd r);
    change_slprop (dlist_snoc left head tail (next (Ghost.reveal (Ghost.hide c))) (econs c (snd r)))
                  (dlist_cons left head tail head' (erev (econs c (snd r))))
                  (fun _ -> dlist_cons_snoc left head tail (next c) (erev (econs c (snd r)));
                         rev_involutive (c :: snd r));

    let r' = elim_dlist_cons_head head' in
    let old' = read head' in
    let c' = { old' with prev = tail } in
    assert (xs' == econs old' (snd r'));

    write head' c';
    slassert (pts_to head' c' `star`
              dlist_cons head' (next (fst r')) tail' right' (snd r'));

    change_slprop
      (dlist_cons head' (next (fst r')) tail' right' (snd r'))
      (dlist_cons head' (next (Ghost.reveal (Ghost.hide c'))) tail' right' (snd r'))
      (fun _ -> ());

    intro_dlist_cons_cons head' tail' right' (hide c') (snd r');

    change_slprop (dlist_cons (prev (reveal (hide c'))) head' tail' right' (econs (hide c') (snd r')))
                  (dlist_cons tail head' tail' right' (econs (hide c') (snd r')))
                  (fun _ -> ());

    rev_cons c (snd r);
    assert (erev (econs c (snd r)) == esnoc (erev (snd r)) c);
    let res : elist (cell a) = esnoc (erev (snd r)) c `eappend` (econs c' (snd r')) in
    datas_rev_snoc_cons (erev (snd r)) (snd r') old old' c c';
    assert (datas res == datas (xs `eappend` xs'));

    change_slprop (dlist_cons left head tail head' (erev (econs c (snd r))) `star`
                   dlist_cons tail head' tail' right' (econs c' (snd r')))
                  (dlist_cons left head tail' right' res)
                  (fun _ -> dlist_cons_concat left head tail head'
                            (List.rev (c :: snd r))
                            tail' right'
                            (c' :: snd r'));
    slassert (dlist_cons left head tail' right' (reveal res));
    res

[@@__reduce__]
let dl (#a:_) (left head tail right: t a) (x:elist a) =
  h_exists (fun (xs:elist (cell a)) ->
    pure (datas xs == x) `star`
    dlist_cons left head tail right xs)

let witness_dl #u (#a:_) (left head tail right:t a) (x:elist a)
  : SteelGhostT (elist (cell a)) u
    (dl left head tail right x)
    (fun (xs:elist (cell a)) ->
      pure (datas xs == x) `star`
      dlist_cons left head tail right xs)
  = let x : erased (elist _) = witness_h_exists () in
    reveal x

let intro_dl #u (#a:_) (left head tail right:t a) (x:elist a) (xs:elist (cell a))
  : SteelGhost unit u
               (dlist_cons left head tail right xs)
               (fun _ -> dl left head tail right x)
               (requires fun _ -> datas xs == x)
               (ensures fun _ _ _ -> True)
  = intro_pure (datas xs == x);
    intro_exists xs (fun (xs:elist (cell a)) ->       pure (datas xs == x) `star`
      dlist_cons left head tail right xs)


let append (#a:_) (left head tail right: t a)
                  (left' head' tail' right': t a)
                  (xs xs':elist a)
  : Steel unit
          (dl left head tail right xs `star` dl left' head' tail' right' xs')
          (fun _ -> dl left head tail' right' (eappend xs xs'))
          (requires fun _ -> Cons? xs /\ Cons? xs')
          (ensures fun _ _ _ -> True)
  = let cs = witness_dl left head tail right xs in
    elim_pure();
    let cs' = witness_dl left' head' tail' right' xs' in
    elim_pure();
    assume (Cons? cs /\ Cons? cs');
    let res = concat left head tail right left' head' tail' right' cs cs' in
    assert (datas cs == xs);
    assert (datas cs' == xs');
    assume (datas res == eappend xs xs');
    intro_dl left head tail' right' (eappend xs xs') res
